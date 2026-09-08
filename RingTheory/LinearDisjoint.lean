/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import Mathlib.Algebra.Algebra.Subalgebra.Rank
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
public import Mathlib.RingTheory.Adjoin.Dimension
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Trace.Defs

/-!

# Linearly disjoint subalgebras

This file contains basics about linearly disjoint subalgebras.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean` for details.

## Main definitions

- `Subalgebra.LinearDisjoint`: two subalgebras are linearly disjoint, if they are
  linearly disjoint as submodules (`Submodule.LinearDisjoint`).

- `Subalgebra.LinearDisjoint.mulMap`: if two subalgebras `A` and `B` of `S / R` are
  linearly disjoint, then there is `A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.

## Main results

### Equivalent characterization of linear disjointness

- `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`:
  if `A` and `B` are linearly disjoint, and if `B` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `A`, they are also `B`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_left_op`:
  conversely, if a basis of `A` is also `B`-linearly independent, then `A` and `B` are
  linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`:
  if `A` and `B` are linearly disjoint, and if `A` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `B`, they are also `A`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_right`:
  conversely, if a basis of `B` is also `A`-linearly independent,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `A` and `B` are linearly disjoint, and if one of `A` and `B` is flat, then for any family of
  `R`-linearly independent elements `{ a_i }` of `A`, and any family of
  `R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
  also `R`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_mul`:
  conversely, if `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
  such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
  then `A` and `B` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `Subalgebra.LinearDisjoint.isDomain_of_injective`,
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`:
  under some flatness and injectivity conditions, if `A` and `B` are `R`-algebras, then `A ⊗[R] B`
  is a domain if and only if there exists an `R`-algebra which is a field that `A` and `B`
  embed into with linearly disjoint images.

- `Subalgebra.LinearDisjoint.of_isField`, `Subalgebra.LinearDisjoint.of_isField'`:
  if `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint, moreover, for any
  `R`-algebra `S` and injections of `A` and `B` into `S`, their images are linearly disjoint.

- `Algebra.TensorProduct.not_isField_of_transcendental`,
  `Algebra.TensorProduct.isAlgebraic_of_isField`:
  if `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
  be a field, equivalently, if `A ⊗[R] B` is a field, then one of them is algebraic.

### Other main results

- `Subalgebra.LinearDisjoint.symm_of_commute`, `Subalgebra.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Subalgebra.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Subalgebra.LinearDisjoint.bot_left`, `Subalgebra.LinearDisjoint.bot_right`:
  the image of `R` in `S` is linearly disjoint with any other subalgebras.

- `Subalgebra.LinearDisjoint.sup_free_of_free`: the compositum of two linearly disjoint
  subalgebras is a free module, if two subalgebras are also free modules.

- `Subalgebra.LinearDisjoint.rank_sup_of_free`,
  `Subalgebra.LinearDisjoint.finrank_sup_of_free`:
  if subalgebras `A` and `B` are linearly disjoint and they are
  free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`:
  conversely, if `A` and `B` are subalgebras which are free modules of finite rank,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`:
  `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right`:
  if `A` and `B` are linearly disjoint, if `A` is free and `B` is flat (resp. `B` is free and
  `A` is flat), then `[B[A] : B] = [A : R]` (resp. `[A[B] : A] = [B : R]`).
  See also `Subalgebra.adjoin_rank_le`.

- `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`:
  if the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`, `Subalgebra.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, under suitable technical conditions, they are disjoint.

The results with name containing "`of_commute`" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

@[expose] public section

open Module
open scoped TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
/-
**Subalgebra.LinearDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommSemiring R] → [inst_1 : Se
miring S] → [inst_2 : Algebra R S] → Subalgebra R S → Subalgebra R S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodu
les of `S`.
-/
protected abbrev LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)
/-
**Subalgebra.linearDisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：linearDisjoint_iff : A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (
toSubmodule B)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearDisjoint_iff : A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B) :=
  Iff.rfl

variable {A B}

@[nontriviality]
/-
**Subalgebra.LinearDisjoint.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a.LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {A B : Subalgebra R S}   [Subsingleton R], A.LinearDisjoi
nt B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_subsingleton`：∀ {R : Type u} {S : Type v} [i
nst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submod
ule R S}   [Subsingleton R], M…
-/
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton

@[nontriviality]
/-
**Subalgebra.LinearDisjoint.of_subsingleton_top** 是 Mathlib 中的一个定理，位于命名空间 `Subal
gebra.LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {A B : Subalgebra R S}   [Subsingleton S], A.LinearDisjoi
nt B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_subsingleton_top`：∀ {R : Type u} {S : Type v
} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Su
bmodule R S}   [Subsingleton S], M…
-/
theorem LinearDisjoint.of_subsingleton_top [Subsingleton S] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton_top

/-- Linear disjointness is symmetric if elements in the module commute. -/
/-
**Subalgebra.LinearDisjoint.symm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a.LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {A B : Subalgebra R S},   A.LinearDisjoint B → (∀ (a : ↥A
) (b : ↥B), Commute ↑a ↑b) → B.LinearDisjoint A
参数：∀ (a : ↥A) (b : ↥B), Commute ↑a ↑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [i
nst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submod
ule R S},   M.LinearDisjoint N…

--- 原说明 ---
Linear disjointness is symmetric if elements in the module commute.
-/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

/-- Linear disjointness is symmetric if elements in the module commute. -/
/-
**Subalgebra.linearDisjoint_comm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a`。
形式化陈述：linearDisjoint_comm_of_commute (hc : forall (a : A) (b : B), Commute a.1 b
.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A
参数：hc : forall (a : A) (b : B), Commute a.1 b.1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [
inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {A B : Subal
gebra R S},   A.LinearDisjoint …
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a

--- 原说明 ---
Linear disjointness is symmetric if elements in the module commute.
-/
theorem linearDisjoint_comm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

/-- Linear disjointness is preserved by injective algebra homomorphisms. -/
/-
**Subalgebra.LinearDisjoint.map** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisj
oint`。
形式化陈述：map (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T] (f : 
S ->ₐ[R] T) (hf : Function.Injective f) : (A.map f).LinearDisjoint (B.map f)
参数：H : A.LinearDisjoint B；f : S ->ₐ[R] T；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.map`：map (H : M.LinearDisjoint N) {T : Type w} 
[Semiring T] [Algebra R T] (f : S ->ₐ[R] T) (hf : Function.Injective f) : (M.map
 (f : S ->ₗ[R] T))…

--- 原说明 ---
Linear disjointness is preserved by injective algebra homomorphisms.
-/
theorem map (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T]
    (f : S →ₐ[R] T) (hf : Function.Injective f) : (A.map f).LinearDisjoint (B.map f) :=
  Submodule.LinearDisjoint.map H f hf

variable (A B)

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
/-
**Subalgebra.LinearDisjoint.bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Linea
rDisjoint`。
形式化陈述：bot_left : (⊥ : Subalgebra R S).LinearDisjoint B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.LinearDisjoint.eq_1`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (A B : Subalgebra R S),
   A.LinearDisjoint …
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.LinearDisjoint.one_left`：one_left : (1 : Submodule R S).Linear
Disjoint N

--- 原说明 ---
The image of `R` in `S` is linearly disjoint with any other subalgebras.
-/
theorem bot_left : (⊥ : Subalgebra R S).LinearDisjoint B := by
  rw [Subalgebra.LinearDisjoint, Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_left _

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
/-
**Subalgebra.LinearDisjoint.bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Line
arDisjoint`。
形式化陈述：bot_right : A.LinearDisjoint ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.LinearDisjoint.eq_1`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (A B : Subalgebra R S),
   A.LinearDisjoint …
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.LinearDisjoint.one_right`：one_right : M.LinearDisjoint (1 : Su
bmodule R S)

--- 原说明 ---
The image of `R` in `S` is linearly disjoint with any other subalgebras.
-/
theorem bot_right : A.LinearDisjoint ⊥ := by
  rw [Subalgebra.LinearDisjoint, Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_right _

variable (R) in
/-- Images of two `R`-algebras `A` and `B` in `A ⊗[R] B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.include_range** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.
LinearDisjoint`。
形式化陈述：include_range (A : Type v) [Semiring A] (B : Type w) [Semiring B] [Algebra
 R A] [Algebra R B] : (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] 
B).range.LinearDisjoint (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[
R] B).range
参数：A : Type v；B : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.LinearDisjoint.eq_1`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (A B : Subalgebra R S),
   A.LinearDisjoint …
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap`：linearEq
uivIncludeRange_symm_toLinearMap : (linearEquivIncludeRange R S T).symm.toLinear
Map = includeLeft.toLinearMap.range.mulMap includeRi…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
Images of two `R`-algebras `A` and `B` in `A ⊗[R] B` are linearly disjoint.
-/
theorem include_range (A : Type v) [Semiring A] (B : Type w) [Semiring B]
    [Algebra R A] [Algebra R B] :
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range.LinearDisjoint
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range := by
  rw [Subalgebra.LinearDisjoint, Submodule.linearDisjoint_iff]
  change Function.Injective <|
    Submodule.mulMap (LinearMap.range Algebra.TensorProduct.includeLeft.toLinearMap)
      (LinearMap.range Algebra.TensorProduct.includeRight.toLinearMap)
  rw [← Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap]
  exact LinearEquiv.injective _

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-- Linear disjointness is symmetric in a commutative ring. -/
/-
**Subalgebra.LinearDisjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.LinearDis
joint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 S] [inst_2 : Algebra R S]   {A B : Subalgebra R S}, A.LinearDisjoint B → B.Line
arDisjoint A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [
inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {A B : Subal
gebra R S},   A.LinearDisjoint …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Linear disjointness is symmetric in a commutative ring.
-/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linear disjointness is symmetric in a commutative ring. -/
/-
**Subalgebra.linearDisjoint_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…

--- 原说明 ---
Linear disjointness is symmetric in a commutative ring.
-/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

/-- Two subalgebras `A`, `B` in a commutative ring are linearly disjoint if and only if
`Subalgebra.mulMap A B` is injective. -/
/-
**Subalgebra.linearDisjoint_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`
。
形式化陈述：linearDisjoint_iff_injective : A.LinearDisjoint B ↔ Function.Injective (A.
mulMap B)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjoint B ↔
 (toSubmodule A).LinearDisjoint (toSubmodule B)
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two subalgebras `A`, `B` in a commutative ring are linearly disjoint if and only
 if
`Subalgebra.mulMap A B` is injective.
-/
theorem linearDisjoint_iff_injective : A.LinearDisjoint B ↔ Function.Injective (A.mulMap B) := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  rfl

namespace LinearDisjoint

variable (H : A.LinearDisjoint B)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`. -/
/-
**Subalgebra.LinearDisjoint.mulMap** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra.LinearD
isjoint`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommSemiring R] →       [inst_
1 : CommSemiring S] →         [inst_2 : Algebra R S] → {A B : Subalgebra R S} → 
A.LinearDisjoint B → TensorProduct R ↥A ↥B ≃ₐ[R] ↥(A ⊔ B)
参数：A ⊔ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mulMap_range`：mulMap_range : (A.mulMap B).range = A ⊔ B

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if the
y are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.
-/
protected def mulMap :=
  (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
/-
**Subalgebra.LinearDisjoint.val_mulMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a.LinearDisjoint`。
形式化陈述：val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a otimesₜ[R] b) : S) = a.1 * 
b.1
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

/--
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` over `R`
such that `A ⊔ B = S`, then this is the natural isomorphism
`A ⊗[R] B ≃ₐ[A] S` induced by multiplication in `S`.
-/
/-
**Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop** 是 Mathlib 中的一个定义，位于命名空间 `Suba
lgebra.LinearDisjoint`。
形式化陈述：mulMapLeftOfSupEqTop (H' : A ⊔ B = ⊤) : A otimes[R] B ≃ₐ[A] S
参数：H' : A ⊔ B = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` ov
er `R`
such that `A ⊔ B = S`, then this is the natural isomorphism
`A ⊗[R] B ≃ₐ[A] S` induced by multiplication in `S`.
-/
noncomputable def mulMapLeftOfSupEqTop (H' : A ⊔ B = ⊤) :
    A ⊗[R] B ≃ₐ[A] S :=
  (AlgEquiv.ofInjective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A S) B.val) H.injective).trans ((Subalgebra.equivOfEq _ _ (by
      apply Subalgebra.restrictScalars_injective R
      rw [restrictScalars_top, ← H']
      exact mulMap_range A B)).trans Subalgebra.topEquiv)

@[simp]
/-
**Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop_tmul** 是 Mathlib 中的一个定理，位于命名空间 
`Subalgebra.LinearDisjoint`。
形式化陈述：mulMapLeftOfSupEqTop_tmul (H' : A ⊔ B = ⊤) (a : A) (b : B) : H.mulMapLeftO
fSupEqTop H' (a otimesₜ[R] b) = (a : S) * (b : S)
参数：H' : A ⊔ B = ⊤；a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem mulMapLeftOfSupEqTop_tmul (H' : A ⊔ B = ⊤) (a : A) (b : B) :
    H.mulMapLeftOfSupEqTop H' (a ⊗ₜ[R] b) = (a : S) * (b : S) := rfl

/--
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` over `R`
such that `A ⊔ B = S`, then any `R`-basis of `B` is also an `A`-basis of `S`.
-/
/-
**Subalgebra.LinearDisjoint.basisOfBasisRight** 是 Mathlib 中的一个定义，位于命名空间 `Subalge
bra.LinearDisjoint`。
形式化陈述：basisOfBasisRight (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) : Basis ι
 A S
参数：H' : A ⊔ B = ⊤；b : Basis ι R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` ov
er `R`
such that `A ⊔ B = S`, then any `R`-basis of `B` is also an `A`-basis of `S`.
-/
noncomputable def basisOfBasisRight (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) :
    Basis ι A S :=
  (b.baseChange A).map (H.mulMapLeftOfSupEqTop H').toLinearEquiv

@[simp]
/-
**Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_apply** 是 Mathlib 中的一个定
理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：algebraMap_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis
 ι R B) (i : ι) : H.basisOfBasisRight H' b i = algebraMap B S (b i)
参数：H' : A ⊔ B = ⊤；b : Basis ι R B；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Basis.baseChange_apply`：baseChange_apply (b : Basis ι R M) (i) : 
b.baseChange S i = 1 otimesₜ b i
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B S (b i) := by
  simp [basisOfBasisRight]

@[simp]
/-
**Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop_symm_apply** 是 Mathlib 中的一个定理，位
于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：mulMapLeftOfSupEqTop_symm_apply (H' : A ⊔ B = ⊤) (x : B) : (H.mulMapLeftOf
SupEqTop H').symm x = 1 otimesₜ[R] x
参数：H' : A ⊔ B = ⊤；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulMapLeftOfSupEqTop_symm_apply (H' : A ⊔ B = ⊤) (x : B) :
    (H.mulMapLeftOfSupEqTop H').symm x = 1 ⊗ₜ[R] x :=
  (H.mulMapLeftOfSupEqTop H').symm_apply_eq.mpr (by simp)
/-
**Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_repr_apply** 是 Mathlib 
中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：algebraMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : 
Basis ι R B) (x : B) (i : ι) : algebraMap A S ((H.basisOfBasisRight H' b).repr x
 i) = algebraMap R S (b.repr x i)
参数：H' : A ⊔ B = ⊤；b : Basis ι R B；x : B；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop_symm_apply`：mulMapLeftOfS
upEqTop_symm_apply (H' : A ⊔ B = ⊤) (x : B) : (H.mulMapLeftOfSupEqTop H').symm x
 = 1 otimesₜ[R] x
· 使用引理 `Module.Basis.baseChange_repr_tmul`：baseChange_repr_tmul (b : Basis ι R M
) (x y i) : (b.baseChange S).repr (x otimesₜ y) i = b.repr y i • x
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B)
    (x : B) (i : ι) :
    algebraMap A S ((H.basisOfBasisRight H' b).repr x i) = algebraMap R S (b.repr x i) := by
  simp [basisOfBasisRight, Algebra.algebraMap_eq_smul_one]
/-
**Subalgebra.LinearDisjoint.leftMulMatrix_basisOfBasisRight_algebraMap** 是 Mathl
ib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：leftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [F
intype ι] [DecidableEq ι] (b : Basis ι R B) (x : B) : Algebra.leftMulMatrix (H.b
asisOfBasisRight H' b) (algebraMap B S x) = RingHom.mapMatrix (algebraMap R A) (
Algebra.leftMulMatrix b x)
参数：H' : A ⊔ B = ⊤；b : Basis ι R B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.leftMulMatrix_eq_repr_mul`：leftMulMatrix_eq_repr_mul (x : S) (i 
j) : leftMulMatrix b x i j = b.repr (x * b j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_apply`：algebraMap
_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) 
: H.basisOfBasisRight H' b i = algebraMap B S (b i…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_repr_apply`：algeb
raMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B
) (x : B) (i : ι) : algebraMap A S ((H.basisOfBasisRigh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R B) (x : B) :
    Algebra.leftMulMatrix (H.basisOfBasisRight H' b) (algebraMap B S x) =
      RingHom.mapMatrix (algebraMap R A) (Algebra.leftMulMatrix b x) := by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← H.algebraMap_basisOfBasisRight_repr_apply H']

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then any `R`-basis of `A` is also a `B`-basis of `S`.
-/
/-
**Subalgebra.LinearDisjoint.basisOfBasisLeft** 是 Mathlib 中的一个定义，位于命名空间 `Subalgeb
ra.LinearDisjoint`。
形式化陈述：basisOfBasisLeft (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) : Basis ι 
B S
参数：H' : A ⊔ B = ⊤；b : Basis ι R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if the
y are
linearly disjoint and such that `A ⊔ B = S`, then any `R`-basis of `A` is also a
 `B`-basis of `S`.
-/
noncomputable def basisOfBasisLeft (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) :
    Basis ι B S :=
  (b.baseChange B).map (H.symm.mulMapLeftOfSupEqTop (by rwa [sup_comm])).toLinearEquiv

@[simp]
/-
**Subalgebra.LinearDisjoint.basisOfBasisLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra.LinearDisjoint`。
形式化陈述：basisOfBasisLeft_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i :
 ι) : H.basisOfBasisLeft H' b i = algebraMap A S (b i)
参数：H' : A ⊔ B = ⊤；b : Basis ι R A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_apply`：algebraMap
_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) 
: H.basisOfBasisRight H' b i = algebraMap B S (b i…
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem basisOfBasisLeft_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A S (b i) :=
  H.symm.algebraMap_basisOfBasisRight_apply (by rwa [sup_comm]) b i
/-
**Subalgebra.LinearDisjoint.basisOfBasisLeft_repr_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Subalgebra.LinearDisjoint`。
形式化陈述：basisOfBasisLeft_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
 (x : A) (i : ι) : algebraMap B S ((H.basisOfBasisLeft H' b).repr x i) = algebra
Map R S (b.repr x i)
参数：H' : A ⊔ B = ⊤；b : Basis ι R A；x : A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_repr_apply`：algeb
raMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B
) (x : B) (i : ι) : algebraMap A S ((H.basisOfBasisRigh…
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem basisOfBasisLeft_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
    (x : A) (i : ι) :
    algebraMap B S ((H.basisOfBasisLeft H' b).repr x i) = algebraMap R S (b.repr x i) :=
  H.symm.algebraMap_basisOfBasisRight_repr_apply (by rwa [sup_comm]) b x i

include H in
/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, and if they are free `R`-modules, then `A ⊔ B` is also a free `R`-module. -/
/-
**Subalgebra.LinearDisjoint.sup_free_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra.LinearDisjoint`。
形式化陈述：sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔
 B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if the
y are
linearly disjoint, and if they are free `R`-modules, then `A ⊔ B` is also a free
 `R`-module.
-/
theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

include H in
/-- If `A` and `B` are subalgebras in a domain `S` over `R`, and if they are
linearly disjoint, then `A ⊗[R] B` is also a domain. -/
/-
**Subalgebra.LinearDisjoint.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Linea
rDisjoint`。
形式化陈述：isDomain [IsDomain S] : IsDomain (A otimes[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…

--- 原说明 ---
If `A` and `B` are subalgebras in a domain `S` over `R`, and if they are
linearly disjoint, then `A ⊗[R] B` is also a domain.
-/
theorem isDomain [IsDomain S] : IsDomain (A ⊗[R] B) :=
  H.injective.isDomain (A.mulMap B).toRingHom

/-- If `A` and `B` are `R`-algebras, such that there exists a domain `S` over `R`
such that `A` and `B` inject into it and their images are linearly disjoint,
then `A ⊗[R] B` is also a domain. -/
/-
**Subalgebra.LinearDisjoint.isDomain_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sub
algebra.LinearDisjoint`。
形式化陈述：isDomain_of_injective [IsDomain S] {A B : Type*} [Semiring A] [Semiring B]
 [Algebra R A] [Algebra R B] {fa : A ->ₐ[R] S} {fb : B ->ₐ[R] S} (hfa : Function
.Injective fa) (hfb : Function.Injective fb) (H : fa.range.LinearDisjoint fb.ran
ge) : IsDomain (A otimes[R] B)
参数：hfa : Function.Injective fa；hfb : Function.Injective fb；H : fa.range.LinearDi
sjoint fb.range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.isDomain`：isDomain [IsDomain S] : IsDomain (A 
otimes[R] B)
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…

--- 原说明 ---
If `A` and `B` are `R`-algebras, such that there exists a domain `S` over `R`
such that `A` and `B` inject into it and their images are linearly disjoint,
then `A ⊗[R] B` is also a domain.
-/
theorem isDomain_of_injective [IsDomain S] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {fa : A →ₐ[R] S} {fb : B →ₐ[R] S}
    (hfa : Function.Injective fa) (hfb : Function.Injective fb)
    (H : fa.range.LinearDisjoint fb.range) : IsDomain (A ⊗[R] B) :=
  have := H.isDomain
  (Algebra.TensorProduct.congr
    (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)).toMulEquiv.isDomain

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-
**Subalgebra.LinearDisjoint.mulLeftMap_ker_eq_bot_iff_linearIndependent_op** 是 M
athlib 中的一个引理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι -> A) : 
LinearMap.ker (Submodule.mulLeftMap (M
参数：a : ι -> A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Finsupp.mapRange.linearEquiv_toLinearMap`：∀ {α : Type u_1} {M : Type u_2
} {N : Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Se
miring R₂]   [inst_2 : AddComm…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Submodule.mulLeftMap_apply_single`：mulLeftMap_apply_single {M N : Submod
ule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N) : mulLeftMap N m (Finsupp.sing
le i n) = (m i).1 * n.1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι → A) :
    LinearMap.ker (Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ B) →ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι →₀ B) →ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (linearEquivOp B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
      EquivLike.injective_comp, LinearMap.coe_restrictScalars]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.mulLeftMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `A`, they are also `B`-linearly independent
in the opposite ring. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_left_op_of_flat** 是 Mathlib 中的一个定理
，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R 
B] {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) : LinearIndependent B.o
p (MulOpposite.op ∘ A.val ∘ a)
参数：H : A.LinearDisjoint B；ha : LinearIndependent R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_left_of_flat`：linearIndepende
nt_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N] {ι : Type*} {m : ι ->
 M} (hm : LinearIndependent R m) : LinearMap.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subalgebra.LinearDisjoint.mulLeftMap_ker_eq_bot_iff_linearIndependent_op
`：mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι -> A) : Line
arMap.ker (Submodule.mulLeftMap (M

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `B` is a flat `R`-module, then for any 
family of
`R`-linearly independent elements of `A`, they are also `B`-linearly independent
in the opposite ring.
-/
theorem linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) :
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

/-- If a basis of `A` is also `B`-linearly independent in the opposite ring,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_basis_left_op** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra.LinearDisjoint`。
形式化陈述：of_basis_left_op {ι : Type*} (a : Basis ι R A) (H : LinearIndependent B.op
 (MulOpposite.op ∘ A.val ∘ a)) : A.LinearDisjoint B
参数：a : Basis ι R A；H : LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_basis_left`：of_basis_left {ι : Type*} (m : B
asis ι R M) (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subalgebra.LinearDisjoint.mulLeftMap_ker_eq_bot_iff_linearIndependent_op
`：mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι -> A) : Line
arMap.ker (Submodule.mulLeftMap (M

--- 原说明 ---
If a basis of `A` is also `B`-linearly independent in the opposite ring,
then `A` and `B` are linearly disjoint.
-/
theorem of_basis_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H
/-
**Subalgebra.LinearDisjoint.mulRightMap_ker_eq_bot_iff_linearIndependent** 是 Mat
hlib 中的一个引理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι -> B) : Li
nearMap.ker (Submodule.mulRightMap (toSubmodule A) (N
参数：b : ι -> B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Submodule.mulRightMap_apply_single`：mulRightMap_apply_single {M N : Subm
odule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M) : mulRightMap M n (Finsupp.s
ingle i m) = m.1 * (n i)…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι → B) :
    LinearMap.ker (Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ A) →ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι →₀ A) →ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.linearCombination_single, i, j]
  exact Submodule.mulRightMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `B`, they are also `A`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_right_of_flat** 是 Mathlib 中的一个定理，位
于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
 {ι : Type*} {b : ι -> B} (hb : LinearIndependent R b) : LinearIndependent A (B.
val ∘ b)
参数：H : A.LinearDisjoint B；hb : LinearIndependent R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_right_of_flat`：linearIndepend
ent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M] {ι : Type*} {n : ι 
-> N} (hn : LinearIndependent R n) : LinearMap…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subalgebra.LinearDisjoint.mulRightMap_ker_eq_bot_iff_linearIndependent`：
mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι -> B) : LinearMa
p.ker (Submodule.mulRightMap (toSubmodule A) (N

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `A` is a flat `R`-module, then for any 
family of
`R`-linearly independent elements of `B`, they are also `A`-linearly independent
.
-/
theorem linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι → B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

/-- If a basis of `B` is also `A`-linearly independent, then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_basis_right** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
.LinearDisjoint`。
形式化陈述：of_basis_right {ι : Type*} (b : Basis ι R B) (H : LinearIndependent A (B.v
al ∘ b)) : A.LinearDisjoint B
参数：b : Basis ι R B；H : LinearIndependent A (B.val ∘ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_basis_right`：of_basis_right {ι : Type*} (n :
 Basis ι R N) (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subalgebra.LinearDisjoint.mulRightMap_ker_eq_bot_iff_linearIndependent`：
mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι -> B) : LinearMa
p.ker (Submodule.mulRightMap (toSubmodule A) (N

--- 原说明 ---
If a basis of `B` is also `A`-linearly independent, then `A` and `B` are linearl
y disjoint.
-/
theorem of_basis_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

variable {A B} in
/-- If `A` and `B` are linearly disjoint and their elements commute, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_left_of_flat_of_commute** 是 Mathli
b 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module
.Flat R B] {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) (hc : forall (a
 : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a)
参数：H : A.LinearDisjoint B；ha : LinearIndependent R a；hc : forall (a : A) (b : B)
, Commute a.1 b.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`：linearIndepen
dent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A] {ι : Type*} {b : ι
 -> B} (hb : LinearIndependent R b) : LinearInd…
· 使用定理 `Subalgebra.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [
inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {A B : Subal
gebra R S},   A.LinearDisjoint …

--- 原说明 ---
If `A` and `B` are linearly disjoint and their elements commute, if `B` is a fla
t `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent.
-/
theorem linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).linearIndependent_right_of_flat ha

/-- If a basis of `A` is also `B`-linearly independent, if elements in `A` and `B` commute,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_basis_left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `
Subalgebra.LinearDisjoint`。
形式化陈述：of_basis_left_of_commute {ι : Type*} (a : Basis ι R A) (H : LinearIndepend
ent B (A.val ∘ a)) (hc : forall (a : A) (b : B), Commute a.1 b.1) : A.LinearDisj
oint B
参数：a : Basis ι R A；H : LinearIndependent B (A.val ∘ a)；hc : forall (a : A) (b : 
B), Commute a.1 b.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [
inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {A B : Subal
gebra R S},   A.LinearDisjoint …
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_right`：of_basis_right {ι : Type*} (b 
: Basis ι R B) (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a

--- 原说明 ---
If a basis of `A` is also `B`-linearly independent, if elements in `A` and `B` c
ommute,
then `A` and `B` are linearly disjoint.
-/
theorem of_basis_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : ∀ (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_basis_right B A a H).symm_of_commute fun _ _ ↦ (hc _ _).symm

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left** 是 Mathlib 中的一个定
理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R
 A] {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndependent R a) (hb : L
inearIndependent R b) : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i.
2).1
参数：H : A.LinearDisjoint B；ha : LinearIndependent R a；hb : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left`：linearIndep
endent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M] {κ ι : Type*}
 {m : κ -> M} {n : ι -> N} (hm : LinearIndependen…

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `A` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_right** 是 Mathlib 中的一个
定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat 
R B] {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndependent R a) (hb : 
LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) => (a i.1).1 * (b i
.2).1
参数：H : A.LinearDisjoint B；ha : LinearIndependent R a；hb : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right`：linearInde
pendent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N] {κ ι : Type
*} {m : κ -> M} {n : ι -> N} (hm : LinearIndepende…

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if one of `A` and `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat** 是 Mathlib 中的一个定理，位于命
名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat (H : A.LinearDisjoint B) (hf : Module.Flat R
 A ∨ Module.Flat R B) {κ ι : Type*} {a : κ -> A} {b : ι -> B} (ha : LinearIndepe
ndent R a) (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) =>
 (a i.1).1 * (b i.2).1
参数：H : A.LinearDisjoint B；hf : Module.Flat R A ∨ Module.Flat R B；ha : LinearInde
pendent R a；hb : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_mul_of_flat`：linearIndependen
t_mul_of_flat (H : M.LinearDisjoint N) (hf : Module.Flat R M ∨ Module.Flat R N) 
{κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm …

--- 原说明 ---
If `A` and `B` are linearly disjoint, if one of `A` and `B` is flat, then for an
y family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

/-- If `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_basis_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.L
inearDisjoint`。
形式化陈述：of_basis_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B) (H : Linear
Independent R fun (i : κ × ι) => (a i.1).1 * (b i.2).1) : A.LinearDisjoint B
参数：a : Basis κ R A；b : Basis ι R B；H : LinearIndependent R fun (i : κ × ι) => (a
 i.1).1 * (b i.2).1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_basis_mul`：of_basis_mul {κ ι : Type*} (m : B
asis κ R M) (n : Basis ι R N) (H : LinearIndependent R fun (i : κ × ι) => (m i.1
).1 * (n i.2).1) : M.Linear…

--- 原说明 ---
If `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
then `A` and `B` are linearly disjoint.
-/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_basis_mul _ _ a b H

variable {A B}

section

variable (H : A.LinearDisjoint B)
include H

/-
**Subalgebra.LinearDisjoint.of_le_left_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Subalg
ebra.LinearDisjoint`。
形式化陈述：of_le_left_of_flat {A' : Subalgebra R S} (h : A' <= A) [Module.Flat R B] :
 A'.LinearDisjoint B
参数：h : A' <= A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat (H : M.L
inearDisjoint N) {M' : Submodule R S} (h : M' <= M) [Module.Flat R N] : M'.Linea
rDisjoint N
-/
theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' ≤ A) [Module.Flat R B] : A'.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_le_left_of_flat H h
/-
**Subalgebra.LinearDisjoint.of_le_right_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Subal
gebra.LinearDisjoint`。
形式化陈述：of_le_right_of_flat {B' : Subalgebra R S} (h : B' <= B) [Module.Flat R A] 
: A.LinearDisjoint B'
参数：h : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat (H : M
.LinearDisjoint N) {N' : Submodule R S} (h : N' <= N) [Module.Flat R M] : M.Line
arDisjoint N'
-/
theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' ≤ B) [Module.Flat R A] : A.LinearDisjoint B' :=
  Submodule.LinearDisjoint.of_le_right_of_flat H h
/-
**Subalgebra.LinearDisjoint.of_le_of_flat_right** 是 Mathlib 中的一个定理，位于命名空间 `Subal
gebra.LinearDisjoint`。
形式化陈述：of_le_of_flat_right {A' B' : Subalgebra R S} (ha : A' <= A) (hb : B' <= B)
 [Module.Flat R B] [Module.Flat R A'] : A'.LinearDisjoint B'
参数：ha : A' <= A；hb : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat {B' :
 Subalgebra R S} (h : B' <= B) [Module.Flat R A] : A.LinearDisjoint B'
· 使用定理 `Subalgebra.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat {A' : S
ubalgebra R S} (h : A' <= A) [Module.Flat R B] : A'.LinearDisjoint B
-/
theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb
/-
**Subalgebra.LinearDisjoint.of_le_of_flat_left** 是 Mathlib 中的一个定理，位于命名空间 `Subalg
ebra.LinearDisjoint`。
形式化陈述：of_le_of_flat_left {A' B' : Subalgebra R S} (ha : A' <= A) (hb : B' <= B) 
[Module.Flat R A] [Module.Flat R B'] : A'.LinearDisjoint B'
参数：ha : A' <= A；hb : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat {A' : S
ubalgebra R S} (h : A' <= A) [Module.Flat R B] : A'.LinearDisjoint B
· 使用定理 `Subalgebra.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat {B' :
 Subalgebra R S} (h : B' <= B) [Module.Flat R A] : A.LinearDisjoint B'
-/
theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_of_inj** 是 Mathli
b 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.F
lat R B) (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Inject
ive (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hf : Module.Flat R A ∨ Module.Flat R B；hc : forall (a b : ↥(A ⊓ B)), Commute 
a.1 b.1；hinj : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`：rank_inf_le
_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) (hc : forall (m
 n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R …
· 使用定理 `lift_rank_range_of_injective`：lift_rank_range_of_injective (f : M ->ₗ[R]
 M') (h : Injective f) : lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'
} (Module.rank R M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_eq_one`：lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ 
a = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 := by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : Cardinal.lift.{u} (Module.rank R (⊥ : Subalgebra R S)) =
      Cardinal.lift.{v} (Module.rank R R) :=
    lift_rank_range_of_injective (Algebra.linearMap R S) hinj
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at this
  rw [← this]
  change Module.rank R (toSubmodule (⊥ : Subalgebra R S)) ≤
    Module.rank R (toSubmodule (A ⊓ B))
  exact Submodule.rank_mono (bot_le : (⊥ : Subalgebra R S) ≤ A ⊓ B)
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_left_of_inj** 是 M
athlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A] (hc : for
all (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Injective (algebraMap R 
S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1；hinj : Function.Injective (alge
braMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_of_inj`：ran
k_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B) 
(hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : F…
-/
theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_right_of_inj** 是 
Mathlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B] (hc : fo
rall (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Injective (algebraMap R
 S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1；hinj : Function.Injective (alge
braMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_of_inj`：ran
k_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B) 
(hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : F…
-/
theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

end

/-
**Subalgebra.LinearDisjoint.rank_eq_one_of_commute_of_flat_of_self_of_inj** 是 Ma
thlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Mo
dule.Flat R A] (hc : forall (a b : A), Commute a.1 b.1) (hinj : Function.Injecti
ve (algebraMap R S)) : Module.rank R A = 1
参数：H : A.LinearDisjoint A；hc : forall (a b : A), Commute a.1 b.1；hinj : Function
.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_left_of_inj
`：rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A] (hc : forall 
(a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Injective …
-/
theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hc : ∀ (a b : A), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then `trace` and `algebraMap` commutes.
-/
/-
**Subalgebra.LinearDisjoint.trace_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra.LinearDisjoint`。
形式化陈述：trace_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R 
B] [Module.Finite R B] (x : B) : Algebra.trace A S (algebraMap B S x) = algebraM
ap R A (Algebra.trace R B x)
参数：H : A.LinearDisjoint B；H' : A ⊔ B = ⊤；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Subalgebra.LinearDisjoint.leftMulMatrix_basisOfBasisRight_algebraMap`：le
ftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι
] [DecidableEq ι] (b : Basis ι R B) (x : B) : Algebra.left…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if the
y are
linearly disjoint and such that `A ⊔ B = S`, then `trace` and `algebraMap` commu
tes.
-/
theorem trace_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.trace A S (algebraMap B S x) = algebraMap R A (Algebra.trace R B x) := by
  simp_rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R B),
    Algebra.trace_eq_matrix_trace (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    Matrix.trace, map_sum, leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply]

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then `norm` and `algebraMap` commutes.
-/
/-
**Subalgebra.LinearDisjoint.norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a.LinearDisjoint`。
形式化陈述：norm_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B
] [Module.Finite R B] (x : B) : Algebra.norm A (algebraMap B S x) = algebraMap R
 A (Algebra.norm R x)
参数：H : A.LinearDisjoint B；H' : A ⊔ B = ⊤；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Subalgebra.LinearDisjoint.leftMulMatrix_basisOfBasisRight_algebraMap`：le
ftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι
] [DecidableEq ι] (b : Basis ι R B) (x : B) : Algebra.left…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if the
y are
linearly disjoint and such that `A ⊔ B = S`, then `norm` and `algebraMap` commut
es.
-/
theorem norm_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.norm A (algebraMap B S x) = algebraMap R A (Algebra.norm R x) := by
  simp_rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R B),
    Algebra.norm_eq_matrix_det (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.map_det]

/-- In a commutative ring, if `A` and `B` are linearly disjoint, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
/-
**Subalgebra.LinearDisjoint.linearIndependent_left_of_flat** 是 Mathlib 中的一个定理，位于
命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B] 
{ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) : LinearIndependent B (A.v
al ∘ a)
参数：H : A.LinearDisjoint B；ha : LinearIndependent R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat_of_commute`：lin
earIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B
] {ι : Type*} {a : ι -> A} (ha : LinearIndependent R a) (…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
In a commutative ring, if `A` and `B` are linearly disjoint, if `B` is a flat `R
`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent.
-/
theorem linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.linearIndependent_left_of_flat_of_commute ha fun _ _ ↦ mul_comm _ _

variable (A B) in
/-- In a commutative ring, if a basis of `A` is also `B`-linearly independent,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_basis_left** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.
LinearDisjoint`。
形式化陈述：of_basis_left {ι : Type*} (a : Basis ι R A) (H : LinearIndependent B (A.va
l ∘ a)) : A.LinearDisjoint B
参数：a : Basis ι R A；H : LinearIndependent B (A.val ∘ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_left_of_commute`：of_basis_left_of_com
mute {ι : Type*} (a : Basis ι R A) (H : LinearIndependent B (A.val ∘ a)) (hc : f
orall (a : A) (b : B), Commute a.1 b.1) …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
In a commutative ring, if a basis of `A` is also `B`-linearly independent,
then `A` and `B` are linearly disjoint.
-/
theorem of_basis_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_basis_left_of_commute A B a H fun _ _ ↦ mul_comm _ _

variable (R) in
/-- If `A` and `B` are flat algebras over `R`, such that `A ⊗[R] B` is a domain, and such that
the algebra maps are injective, then there exists an `R`-algebra `K` that is a field that `A`
and `B` inject into with linearly disjoint images. Note: `K` can chosen to be the
fraction field of `A ⊗[R] B`, but here we hide this fact. -/
/-
**Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective** 是 Mathlib 中的
一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：exists_field_of_isDomain_of_injective (A : Type v) [CommRing A] (B : Type 
w) [CommRing B] [Algebra R A] [Algebra R B] [Module.Flat R A] [Module.Flat R B] 
[IsDomain (A otimes[R] B)] (ha : Function.Injective (algebraMap R A)) (hb : Func
tion.Injective (algebraMap R B)) : exists (K : Type (max v w)) (_ : Field K) (_ 
: Algebra R K) (fa : A ->ₐ[R] K) (fb : B ->ₐ[R] K), Function.Injective fa ∧ Func
tion.Injective fb ∧ fa.range.LinearDisjoint fb.range
参数：A : Type v；B : Type w；A otimes[R] B；ha : Function.Injective (algebraMap R A)；
hb : Function.Injective (algebraMap R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Algebra.TensorProduct.includeLeft_injective`：includeLeft_injective [Modu
le.Flat R A] (hb : Function.Injective (algebraMap R B)) : Function.Injective (in
cludeLeft : A ->ₐ[S] A otimes[R] …
· 使用定理 `Algebra.TensorProduct.includeRight_injective`：includeRight_injective [Mo
dule.Flat R B] (ha : Function.Injective (algebraMap R A)) : Function.Injective (
includeRight : B ->ₐ[R] A otimes[R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.range_comp`：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.com
p f).range = f.range.map g
· 使用定理 `Subalgebra.LinearDisjoint.map`：map (H : A.LinearDisjoint B) {T : Type w}
 [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) (hf : Function.Injective f) : (A.ma
p f).LinearDisjoint…
· 使用定理 `Subalgebra.LinearDisjoint.include_range`：include_range (A : Type v) [Sem
iring A] (B : Type w) [Semiring B] [Algebra R A] [Algebra R B] : (Algebra.Tensor
Product.includeLeft : A ->ₐ[R…

--- 原说明 ---
If `A` and `B` are flat algebras over `R`, such that `A ⊗[R] B` is a domain, and
 such that
the algebra maps are injective, then there exists an `R`-algebra `K` that is a f
ield that `A`
and `B` inject into with linearly disjoint images. Note: `K` can chosen to be th
e
fraction field of `A ⊗[R] B`, but here we hide this fact.
-/
theorem exists_field_of_isDomain_of_injective (A : Type v) [CommRing A] (B : Type w) [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] [Module.Flat R B] [IsDomain (A ⊗[R] B)]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (K : Type (max v w)) (_ : Field K) (_ : Algebra R K) (fa : A →ₐ[R] K) (fb : B →ₐ[R] K),
    Function.Injective fa ∧ Function.Injective fb ∧ fa.range.LinearDisjoint fb.range :=
  let K := FractionRing (A ⊗[R] B)
  let i := IsScalarTower.toAlgHom R (A ⊗[R] B) K
  have hi : Function.Injective i := IsFractionRing.injective (A ⊗[R] B) K
  ⟨K, inferInstance, inferInstance,
    i.comp Algebra.TensorProduct.includeLeft,
    i.comp Algebra.TensorProduct.includeRight,
    hi.comp (Algebra.TensorProduct.includeLeft_injective hb),
    hi.comp (Algebra.TensorProduct.includeRight_injective ha), by
      simpa only [AlgHom.range_comp] using (include_range R A B).map i hi⟩

/-- If `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_isField** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Lin
earDisjoint`。
形式化陈述：of_isField (H : IsField (A otimes[R] B)) : A.LinearDisjoint B
参数：H : IsField (A otimes[R] B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.linearDisjoint_iff_injective`：linearDisjoint_iff_injective : 
A.LinearDisjoint B ↔ Function.Injective (A.mulMap B)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A

--- 原说明 ---
If `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint.
-/
theorem of_isField (H : IsField (A ⊗[R] B)) : A.LinearDisjoint B := by
  nontriviality S
  rw [linearDisjoint_iff_injective]
  let : Field (A ⊗[R] B) := H.toField
  -- need this otherwise `RingHom.injective` does not work
  let : NonAssocRing (A ⊗[R] B) := Ring.toNonAssocRing
  exact RingHom.injective _

/-- If `A ⊗[R] B` is a field, then for any `R`-algebra `S`
and injections of `A` and `B` into `S`, their images are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_isField'** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Li
nearDisjoint`。
形式化陈述：of_isField' {A : Type v} [Ring A] {B : Type w} [Ring B] [Algebra R A] [Alg
ebra R B] (H : IsField (A otimes[R] B)) (fa : A ->ₐ[R] S) (fb : B ->ₐ[R] S) (hfa
 : Function.Injective fa) (hfb : Function.Injective fb) : fa.range.LinearDisjoin
t fb.range
参数：H : IsField (A otimes[R] B)；fa : A ->ₐ[R] S；fb : B ->ₐ[R] S；hfa : Function.In
jective fa；hfb : Function.Injective fb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_isField`：of_isField (H : IsField (A otimes[
R] B)) : A.LinearDisjoint B
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…

--- 原说明 ---
If `A ⊗[R] B` is a field, then for any `R`-algebra `S`
and injections of `A` and `B` into `S`, their images are linearly disjoint.
-/
theorem of_isField' {A : Type v} [Ring A] {B : Type w} [Ring B]
    [Algebra R A] [Algebra R B] (H : IsField (A ⊗[R] B))
    (fa : A →ₐ[R] S) (fb : B →ₐ[R] S) (hfa : Function.Injective fa) (hfb : Function.Injective fb) :
    fa.range.LinearDisjoint fb.range := by
  apply of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa)
    (AlgEquiv.ofInjective fb hfb) |>.symm.toMulEquiv.isField H

-- need to be in this file since it uses linearly disjoint
open Cardinal Polynomial in
variable (R) in
/-- If `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
be a field. -/
/-
**Subalgebra.LinearDisjoint._root_.Algebra.TensorProduct.not_isField_of_transcen
dental** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗
[R] B` cannot
be a field.
-/
theorem _root_.Algebra.TensorProduct.not_isField_of_transcendental
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] [Algebra.Transcendental R A] [Algebra.Transcendental R B] :
    ¬IsField (A ⊗[R] B) := fun H ↦ by
  let := H.toField
  obtain ⟨a, hta⟩ := ‹Algebra.Transcendental R A›
  obtain ⟨b, htb⟩ := ‹Algebra.Transcendental R B›
  have ha : Function.Injective (algebraMap R A) := Algebra.injective_of_transcendental
  have hb : Function.Injective (algebraMap R B) := Algebra.injective_of_transcendental
  let fa : A →ₐ[R] A ⊗[R] B := Algebra.TensorProduct.includeLeft
  let fb : B →ₐ[R] A ⊗[R] B := Algebra.TensorProduct.includeRight
  have hfa : Function.Injective fa := Algebra.TensorProduct.includeLeft_injective hb
  have hfb : Function.Injective fb := Algebra.TensorProduct.includeRight_injective ha
  have := hfa.isDomain fa.toRingHom
  have := hfb.isDomain fb.toRingHom
  have := ha.isDomain _
  have : Module.Flat R (toSubmodule fa.range) :=
    .of_linearEquiv (AlgEquiv.ofInjective fa hfa).symm.toLinearEquiv
  have key1 : Module.rank R ↥(fa.range ⊓ fb.range) ≤ 1 :=
    (include_range R A B).rank_inf_le_one_of_flat_left
  let ga : R[X] →ₐ[R] A := aeval a
  let gb : R[X] →ₐ[R] B := aeval b
  let gab := fa.comp ga
  replace hta : Function.Injective ga := transcendental_iff_injective.1 hta
  replace htb : Function.Injective gb := transcendental_iff_injective.1 htb
  have htab : Function.Injective gab := hfa.comp hta
  algebraize_only [ga.toRingHom, gb.toRingHom]
  let f := Algebra.TensorProduct.mapOfCompatibleSMul R[X] R R A B
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R[X] A B hta htb
  have hf : Function.Injective f := RingHom.injective _
  have key2 : gab.range ≤ fa.range ⊓ fb.range := by
    simp_rw [gab, ga, ← aeval_algHom]
    rw [Algebra.TensorProduct.includeLeft_apply, ← Algebra.adjoin_singleton_eq_range_aeval]
    simp_rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, Algebra.coe_inf, Set.mem_inter_iff,
      AlgHom.coe_range, Set.mem_range]
    refine ⟨⟨a, by simp [fa]⟩, ⟨b, hf ?_⟩⟩
    simp_rw [fb, Algebra.TensorProduct.includeRight_apply, f,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
    convert! ← (TensorProduct.smul_tmul (R := R[X]) (R' := R[X]) (M := A) (N := B) X 1 1).symm <;>
      (simp_rw [Algebra.smul_def, mul_one]; exact aeval_X _)
  have key3 := (Subalgebra.inclusion key2).comp (AlgEquiv.ofInjective gab htab).toAlgHom
    |>.toLinearMap.lift_rank_le_of_injective
      ((Subalgebra.inclusion_injective key2).comp (AlgEquiv.injective _))
  have := lift_uzero.{u} _ ▸ (basisMonomials R).mk_eq_rank.symm
  simp only [this, mk_eq_aleph0, lift_aleph0, aleph0_le_lift] at key3
  exact (key3.trans key1).not_gt one_lt_aleph0

variable (R) in
/-- If `A` and `B` are flat `R`-algebras, such that `A ⊗[R] B` is a field, then one of `A` and `B`
is algebraic over `R`. -/
/-
**Subalgebra.LinearDisjoint._root_.Algebra.TensorProduct.isAlgebraic_of_isField*
* 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are flat `R`-algebras, such that `A ⊗[R] B` is a field, then one 
of `A` and `B`
is algebraic over `R`.
-/
theorem _root_.Algebra.TensorProduct.isAlgebraic_of_isField
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] (H : IsField (A ⊗[R] B)) :
    Algebra.IsAlgebraic R A ∨ Algebra.IsAlgebraic R B := by
  by_contra! h
  simp_rw [← Algebra.transcendental_iff_not_isAlgebraic] at h
  obtain ⟨_, _⟩ := h
  exact Algebra.TensorProduct.not_isField_of_transcendental R A B H

variable (H : A.LinearDisjoint B)

include H in
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_flat_of_inj** 是 Mathlib 中的一个定理，位于
命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B) (h
inj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hf : Module.Flat R A ∨ Module.Flat R B；hinj : Function.Injective (algebraMap 
R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_of_inj`：ran
k_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B) 
(hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ ↦ mul_comm _ _) hinj

include H in
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_flat_left_of_inj** 是 Mathlib 中的一个
定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A] (hinj : Function.Inj
ective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hinj : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_left_of_inj
`：rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A] (hc : forall 
(a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Injective …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ ↦ mul_comm _ _) hinj

include H in
/-
**Subalgebra.LinearDisjoint.rank_inf_eq_one_of_flat_right_of_inj** 是 Mathlib 中的一
个定理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B] (hinj : Function.In
jective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1
参数：hinj : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_inf_eq_one_of_commute_of_flat_right_of_in
j`：rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B] (hc : foral
l (a b : ↥(A ⊓ B)), Commute a.1 b.1) (hinj : Function.Injective…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ ↦ mul_comm _ _) hinj
/-
**Subalgebra.LinearDisjoint.rank_eq_one_of_flat_of_self_of_inj** 是 Mathlib 中的一个定
理，位于命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R
 A] (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1
参数：H : A.LinearDisjoint A；hinj : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.rank_eq_one_of_commute_of_flat_of_self_of_inj`
：rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.
Flat R A] (hc : forall (a b : A), Commute a.1 b.1) (hinj : Fu…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 :=
  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ ↦ mul_comm _ _) hinj

include H in
/-- In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`. -/
/-
**Subalgebra.LinearDisjoint.rank_sup_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra.LinearDisjoint`。
形式化陈述：rank_sup_of_free [Module.Free R A] [Module.Free R B] : Module.rank R ↥(A ⊔
 B) = Module.rank R A * Module.rank R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_tensorProduct'`：rank_tensorProduct' : Module.rank R (M otimes[S] M₁
) = Module.rank R M * Module.rank S M₁
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁

--- 原说明 ---
In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they
 are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A
` and `B`.
-/
theorem rank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct', H.mulMap.toLinearEquiv.rank_eq]

include H in
/-- In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`. -/
/-
**Subalgebra.LinearDisjoint.finrank_sup_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Subal
gebra.LinearDisjoint`。
形式化陈述：finrank_sup_of_free [Module.Free R A] [Module.Free R B] : Module.finrank R
 ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subalgebra.LinearDisjoint.rank_sup_of_free`：rank_sup_of_free [Module.Fre
e R A] [Module.Free R B] : Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.ran
k R B

--- 原说明 ---
In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they
 are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A
` and `B`.
-/
theorem finrank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B := by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup_of_free))

/-- In a commutative ring, if `A` and `B` are subalgebras which are free modules of finite rank,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_finrank_sup_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra.LinearDisjoint`。
形式化陈述：of_finrank_sup_of_free [Module.Free R A] [Module.Free R B] [Module.Finite 
R A] [Module.Finite R B] (H : Module.finrank R ↥(A ⊔ B) = Module.finrank R A * M
odule.finrank R B) : A.LinearDisjoint B
参数：H : Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用引理 `exists_linearIndependent_of_le_finrank`：exists_linearIndependent_of_le_f
inrank {n : Nat} (hn : n <= finrank R M) : exists f : Fin n -> M, LinearIndepend
ent R f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_tensorProduct`：Module.finrank_tensorProduct : finrank R (
M otimes[S] M') = finrank R M * finrank S M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.finrank_finsupp_self`：finrank_finsupp_self {ι : Type v} [Fintype 
ι] : finrank R (ι ->₀ R) = card ι
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `Subalgebra.mulMap'_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (A B : Subalge
bra R S), Function.…
· 使用定理 `Subalgebra.finite_sup`：Subalgebra.finite_sup {K L : Type*} [CommSemiring
 K] [CommSemiring L] [Algebra K L] (E1 E2 : Subalgebra K L) [Module.Finite K E1]
 [Module.Fi…
· 使用定理 `Subalgebra.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjoint B ↔
 (toSubmodule A).LinearDisjoint (toSubmodule B)
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `OrzechProperty.injective_of_surjective_of_injective`：injective_of_surjec
tive_of_injective {N : Type w} [AddCommMonoid N] [Module R N] (i f : N ->ₗ[R] M)
 (hi : Injective i) (hf : Surjective f) :…
· 使用定理 `CommRing.orzechProperty`：∀ (R : Type u_1) [inst : CommRing R], OrzechPro
perty R

--- 原说明 ---
In a commutative ring, if `A` and `B` are subalgebras which are free modules of 
finite rank,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint.
-/
theorem of_finrank_sup_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B]
    (H : Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B) :
    A.LinearDisjoint B := by
  nontriviality R
  rw [← Module.finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent] at hj
  let j' := Finsupp.linearCombination R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A ⊗[R] B) _ (by simp)).toLinearMap
  replace hj : Function.Injective j' := by simpa [j']
  have hf : Function.Surjective (mulMap' A B).toLinearMap := mulMap'_surjective A B
  have := Subalgebra.finite_sup A B
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  exact Subtype.val_injective.comp (OrzechProperty.injective_of_surjective_of_injective j' _ hj hf)

include H in
/-- If `A` and `B` are linearly disjoint, if `A` is free and `B` is flat,
then `[B[A] : B] = [A : R]`. See also `Subalgebra.adjoin_rank_le`. -/
/-
**Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left** 是 Mathlib 中的一个定理，位于命名空间 `
Subalgebra.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B] [Nontrivial R
] [Nontrivial S] : Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R 
A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.rank_toSubmodule`：Subalgebra.rank_toSubmodule (S : Subalgebra
 F E) : Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Subalgebra.adjoin_eq_span_basis`：Subalgebra.adjoin_eq_span_basis {ι : Ty
pe*} (bL : Basis ι F L) : toSubmodule (adjoin E (L : Set K)) = span E (Set.range
 fun i : ι => (bL i).…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`：linearIndepend
ent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B] {ι : Type*} {a : ι -
> A} (ha : LinearIndependent R a) : LinearInde…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `rank_span`：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.
rank R ↑(span R (range v)) = #(range v)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Cardinal.mk_range_eq`：mk_range_eq (f : α -> β) (h : Injective f) : #(ran
ge f) = #α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `A` is free and `B` is flat,
then `[B[A] : B] = [A : R]`. See also `Subalgebra.adjoin_rank_le`.
-/
theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
    [Nontrivial R] [Nontrivial S] :
    Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R A := by
  rw [← rank_toSubmodule, Module.Free.rank_eq_card_chooseBasisIndex R A,
    A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.linearIndependent_left_of_flat (Module.Free.chooseBasis R A).linearIndependent
  rw [rank_span this, Cardinal.mk_range_eq _ this.injective]

include H in
/-- If `A` and `B` are linearly disjoint, if `B` is free and `A` is flat,
then `[A[B] : A] = [B : R]`. See also `Subalgebra.adjoin_rank_le`. -/
/-
**Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right** 是 Mathlib 中的一个定理，位于命名空间 
`Subalgebra.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A] [Nontrivial 
R] [Nontrivial S] : Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R
 B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`：adjoin_rank_eq_rank_
left [Module.Free R A] [Module.Flat R B] [Nontrivial R] [Nontrivial S] : Module.
rank B (Algebra.adjoin B (A : Set S)) = …
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…

--- 原说明 ---
If `A` and `B` are linearly disjoint, if `B` is free and `A` is flat,
then `[A[B] : A] = [B : R]`. See also `Subalgebra.adjoin_rank_le`.
-/
theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
    [Nontrivial R] [Nontrivial S] :
    Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R B :=
  H.symm.adjoin_rank_eq_rank_left

/-- If the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_finrank_coprime_of_free** 是 Mathlib 中的一个定理，位于命名空间
 `Subalgebra.LinearDisjoint`。
形式化陈述：of_finrank_coprime_of_free [Module.Free R A] [Module.Free R B] [Module.Fre
e A (Algebra.adjoin A (B : Set S))] [Module.Free B (Algebra.adjoin B (A : Set S)
)] (H : (Module.finrank R A).Coprime (Module.finrank R B)) : A.LinearDisjoint B
参数：Algebra.adjoin A (B : Set S)；Algebra.adjoin B (A : Set S)；H : (Module.finrank
 R A).Coprime (Module.finrank R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.eq_bot_of_finrank_one`：eq_bot_of_finrank_one (h : finrank F S
 = 1) [Module.Free F S] : S = ⊥
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `Subalgebra.LinearDisjoint.bot_right`：bot_right : A.LinearDisjoint ⊥
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `Subalgebra.LinearDisjoint.bot_left`：bot_left : (⊥ : Subalgebra R S).Line
arDisjoint B
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Subalgebra.finite_sup`：Subalgebra.finite_sup {K L : Type*} [CommSemiring
 K] [CommSemiring L] [Algebra K L] (E1 E2 : Subalgebra K L) [Module.Finite K E1]
 [Module.Fi…
· 使用定理 `LinearMap.finrank_le_finrank_of_injective`：LinearMap.finrank_le_finrank_
of_injective [Module.Finite R M'] {f : M ->ₗ[R] M'} (hf : Function.Injective f) 
: finrank R M <= finrank R M'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`：of_finrank_sup_of_free
 [Module.Free R A] [Module.Free R B] [Module.Finite R A] [Module.Finite R B] (H 
: Module.finrank R ↥(A ⊔ B) = Module.f…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Subalgebra.finrank_sup_le_of_free`：finrank_sup_le_of_free : finrank R ↥(
A ⊔ B) <= finrank R A * finrank R B
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Subalgebra.finrank_left_dvd_finrank_sup_of_free`：finrank_left_dvd_finran
k_sup_of_free : finrank R A ∣ finrank R ↥(A ⊔ B)
· 使用定理 `Subalgebra.finrank_right_dvd_finrank_sup_of_free`：finrank_right_dvd_finr
ank_sup_of_free : finrank R B ∣ finrank R ↥(A ⊔ B)

--- 原说明 ---
If the rank of `A` and `B` are coprime, and they satisfy some freeness condition
,
then `A` and `B` are linearly disjoint.
-/
theorem of_finrank_coprime_of_free [Module.Free R A] [Module.Free R B]
    [Module.Free A (Algebra.adjoin A (B : Set S))] [Module.Free B (Algebra.adjoin B (A : Set S))]
    (H : (Module.finrank R A).Coprime (Module.finrank R B)) : A.LinearDisjoint B := by
  nontriviality R
  by_cases h1 : Module.finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_right _
  by_cases h2 : Module.finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_left _
  have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h1)
  have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h2)
  have := finite_sup A B
  have : Module.finrank R A ≤ Module.finrank R ↥(A ⊔ B) :=
    LinearMap.finrank_le_finrank_of_injective <|
      Submodule.inclusion_injective (show toSubmodule A ≤ toSubmodule (A ⊔ B) by simp)
  exact of_finrank_sup_of_free <| (finrank_sup_le_of_free A B).antisymm <|
    Nat.le_of_dvd (lt_of_lt_of_le (Nat.pos_of_ne_zero h1) this) <| H.mul_dvd_of_dvd_of_dvd
      (finrank_left_dvd_finrank_sup_of_free A B) (finrank_right_dvd_finrank_sup_of_free A B)

variable (A B)

/-- If `A/R` is integral, such that `A'` and `B` are linearly disjoint for all subalgebras `A'`
of `A` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left** 是 Mathlib 中的一个定理，位于命
名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：of_linearDisjoint_finite_left [Algebra.IsIntegral R A] (H : forall A' : Su
balgebra R S, A' <= A -> [Module.Finite R A'] -> A'.LinearDisjoint B) : A.Linear
Disjoint B
参数：H : forall A' : Subalgebra R S, A' <= A -> [Module.Finite R A'] -> A'.LinearD
isjoint B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjoint B ↔
 (toSubmodule A).LinearDisjoint (toSubmodule B)
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `TensorProduct.exists_finite_submodule_left_of_setFinite'`：exists_finite_
submodule_left_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) : exist
s (M' : Submodule R M) (hM : M' <= M₁), Module…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.FG.of_finite`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M
} [Module.Fi…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `A/R` is integral, such that `A'` and `B` are linearly disjoint for all subal
gebras `A'`
of `A` which are finitely generated `R`-modules, then `A` and `B` are linearly d
isjoint.
-/
theorem of_linearDisjoint_finite_left [Algebra.IsIntegral R A]
    (H : ∀ A' : Subalgebra R S, A' ≤ A → [Module.Finite R A'] → A'.LinearDisjoint B) :
    A.LinearDisjoint B := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ : M'.FG := .of_finite
  have hs' : (s : Set S) ⊆ A := by rwa [← hs, Submodule.span_le] at hM
  let A' := Algebra.adjoin R (s : Set S)
  have hf' : Submodule.FG (toSubmodule A') := fg_adjoin_of_finite s.finite_toSet fun x hx ↦
    (isIntegral_algHom_iff A.val Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (R := R) (A := A) ⟨x, hs' hx⟩)
  replace hf' : Module.Finite R A' := .of_fg hf'
  have hA : toSubmodule A' ≤ toSubmodule A := Algebra.adjoin_le_iff.2 hs'
  replace h : {x, y} ⊆ (LinearMap.range (LinearMap.rTensor (toSubmodule B)
      (Submodule.inclusion hA)) : Set _) := fun _ hx ↦ by
    have : Submodule.inclusion hM = Submodule.inclusion hA ∘ₗ Submodule.inclusion
      (show M' ≤ toSubmodule A' by
        rw [← hs, Submodule.span_le]; exact Algebra.adjoin_le_iff.1 (le_refl _)) := rfl
    rw [this, LinearMap.rTensor_comp] at h
    exact LinearMap.range_comp_le_range _ _ (h hx)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H A' hA).injective (by simp [← Submodule.mulMap_comp_rTensor _ hA, hx', hy', hxy])

/-- If `B/R` is integral, such that `A` and `B'` are linearly disjoint for all subalgebras `B'`
of `B` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right** 是 Mathlib 中的一个定理，位于
命名空间 `Subalgebra.LinearDisjoint`。
形式化陈述：of_linearDisjoint_finite_right [Algebra.IsIntegral R B] (H : forall B' : S
ubalgebra R S, B' <= B -> [Module.Finite R B'] -> A.LinearDisjoint B') : A.Linea
rDisjoint B
参数：H : forall B' : Subalgebra R S, B' <= B -> [Module.Finite R B'] -> A.LinearDi
sjoint B'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…
· 使用定理 `Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left`：of_linearDisjoi
nt_finite_left [Algebra.IsIntegral R A] (H : forall A' : Subalgebra R S, A' <= A
 -> [Module.Finite R A'] -> A'.LinearDisjoint…

--- 原说明 ---
If `B/R` is integral, such that `A` and `B'` are linearly disjoint for all subal
gebras `B'`
of `B` which are finitely generated `R`-modules, then `A` and `B` are linearly d
isjoint.
-/
theorem of_linearDisjoint_finite_right [Algebra.IsIntegral R B]
    (H : ∀ B' : Subalgebra R S, B' ≤ B → [Module.Finite R B'] → A.LinearDisjoint B') :
    A.LinearDisjoint B :=
  (of_linearDisjoint_finite_left B A fun B' hB' _ ↦ (H B' hB').symm).symm

variable {A B}

/-- If `A/R` and `B/R` are integral, such that any finite subalgebras in `A` and `B` are
linearly disjoint, then `A` and `B` are linearly disjoint. -/
/-
**Subalgebra.LinearDisjoint.of_linearDisjoint_finite** 是 Mathlib 中的一个定理，位于命名空间 `
Subalgebra.LinearDisjoint`。
形式化陈述：of_linearDisjoint_finite [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
 (H : forall (A' B' : Subalgebra R S), A' <= A -> B' <= B -> [Module.Finite R A'
] -> [Module.Finite R B'] -> A'.LinearDisjoint B') : A.LinearDisjoint B
参数：H : forall (A' B' : Subalgebra R S), A' <= A -> B' <= B -> [Module.Finite R A
'] -> [Module.Finite R B'] -> A'.LinearDisjoint B'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left`：of_linearDisjoi
nt_finite_left [Algebra.IsIntegral R A] (H : forall A' : Subalgebra R S, A' <= A
 -> [Module.Finite R A'] -> A'.LinearDisjoint…
· 使用定理 `Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right`：of_linearDisjo
int_finite_right [Algebra.IsIntegral R B] (H : forall B' : Subalgebra R S, B' <=
 B -> [Module.Finite R B'] -> A.LinearDisjoint…

--- 原说明 ---
If `A/R` and `B/R` are integral, such that any finite subalgebras in `A` and `B`
 are
linearly disjoint, then `A` and `B` are linearly disjoint.
-/
theorem of_linearDisjoint_finite
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (H : ∀ (A' B' : Subalgebra R S), A' ≤ A → B' ≤ B →
      [Module.Finite R A'] → [Module.Finite R B'] → A'.LinearDisjoint B') :
    A.LinearDisjoint B :=
  of_linearDisjoint_finite_left A B fun _ hA' _ ↦
    of_linearDisjoint_finite_right _ B fun _ hB' _ ↦ H _ _ hA' hB'

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-
**Subalgebra.LinearDisjoint.inf_eq_bot_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Sub
algebra.LinearDisjoint`。
形式化陈述：inf_eq_bot_of_commute (H : A.LinearDisjoint B) (hc : forall (a b : ↥(A ⊓ B
)), Commute a.1 b.1) : A ⊓ B = ⊥
参数：H : A.LinearDisjoint B；hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.eq_bot_of_rank_le_one`：eq_bot_of_rank_le_one (h : Module.rank
 F S <= 1) [Module.Free F S] : S = ⊥
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left`：rank_i
nf_le_one_of_commute_of_flat_left [Module.Flat R M] (hc : forall (m n : ↥(M ⊓ N)
), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem inf_eq_bot_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)
/-
**Subalgebra.LinearDisjoint.eq_bot_of_commute_of_self** 是 Mathlib 中的一个定理，位于命名空间 
`Subalgebra.LinearDisjoint`。
形式化陈述：eq_bot_of_commute_of_self (H : A.LinearDisjoint A) (hc : forall (a b : A),
 Commute a.1 b.1) : A = ⊥
参数：H : A.LinearDisjoint A；hc : forall (a b : A), Commute a.1 b.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`：inf_eq_bot_of_commute (
H : A.LinearDisjoint B) (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B 
= ⊥
-/
theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : ∀ (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

/-
**Subalgebra.LinearDisjoint.inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.Lin
earDisjoint`。
形式化陈述：inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥
参数：H : A.LinearDisjoint B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`：inf_eq_bot_of_commute (
H : A.LinearDisjoint B) (hc : forall (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B 
= ⊥
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥ :=
  H.inf_eq_bot_of_commute fun _ _ ↦ mul_comm _ _
/-
**Subalgebra.LinearDisjoint.eq_bot_of_self** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
.LinearDisjoint`。
形式化陈述：eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥
参数：H : A.LinearDisjoint A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.eq_bot_of_commute_of_self`：eq_bot_of_commute_o
f_self (H : A.LinearDisjoint A) (hc : forall (a b : A), Commute a.1 b.1) : A = ⊥
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ ↦ mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra

