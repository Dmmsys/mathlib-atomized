/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor product of graded algebra

In this file we show that if `𝒜` is a graded `R`-algebra, and `S` is any `R`-algebra, then
`S ⊗[R] 𝒜` is a graded `S`-algebra with the grading `fun i ↦ (𝒜 i).baseChange S`.

## Implementation notes

We need to provide the shortcut instances afterwards for the grade zero because it is expensive to
deduce via unification the function `fun i ↦ (𝒜 i).baseChange S`.
-/

@[expose] public section

open TensorProduct Submodule SetLike

namespace GradedAlgebra

variable {ι R A S : Type*}

section Semiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

set_option backward.isDefEq.respectTransparency.types false in
/-
**GradedAlgebra.baseChange** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
形式化陈述：baseChange : GradedAlgebra fun i => (𝒜 i).baseChange S where one_mem
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance baseChange : GradedAlgebra fun i ↦ (𝒜 i).baseChange S where
  one_mem := tmul_mem_baseChange_of_mem _ <| one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S ⊗[R] A)) ((𝒜 j).baseChange S) ≤
      (𝒜 (i + j)).baseChange S from fun xi xj ↦ (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le, Set.image2_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simpa using subset_span <| Set.mem_image_of_mem _ <| mul_mem_graded hx hy
/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring ((𝒜 0).baseChange S) :=
  GradeZero.instSemiring fun i ↦ (𝒜 i).baseChange S
/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra S ((𝒜 0).baseChange S) :=
  GradeZero.instAlgebra fun i ↦ (𝒜 i).baseChange S
/-
**GradedAlgebra.coe_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_3} {S : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : Decidab
leEq ι] [inst_4 : AddMonoid ι] [inst_5 : Semiring A] [inst_6 : Algebra R A]   (𝒜
 : ι → Submodule R A) [inst_7 : GradedAlgebra 𝒜] (s : S),   ↑((algebraMap S ↥(Su
bmodule.baseChange S (𝒜 0))) s) = s ⊗ₜ[R] 1
参数：𝒜 : ι → Submodule R A；s : S；(algebraMap S ↥(Submodule.baseChange S (𝒜 0))) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma coe_algebraMap_apply (s : S) :
    (algebraMap _ ((𝒜 0).baseChange S) s : S ⊗[R] A) = s ⊗ₜ 1 := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring ((𝒜 0).baseChange S) :=
  GradeZero.instCommSemiring fun i ↦ (𝒜 i).baseChange S

end CommSemiring

section Algebra
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra ((𝒜 0).baseChange S) (S ⊗[R] A) :=
  GradeZero.instAlgebraSubtypeMemOfNat fun i ↦ (𝒜 i).baseChange S
/-
**GradedAlgebra.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_3} {S : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : Decidab
leEq ι] [inst_4 : AddCommMonoid ι] [inst_5 : CommSemiring A]   [inst_6 : Algebra
 R A] (𝒜 : ι → Submodule R A) [inst_7 : GradedAlgebra 𝒜] (x : ↥(Submodule.baseCh
ange S (𝒜 0))),   (algebraMap (↥(Submodule.baseChange S (𝒜 0))) (TensorProduct R
 S A)) x = ↑x
参数：𝒜 : ι → Submodule R A；x : ↥(Submodule.baseChange S (𝒜 0))；algebraMap (↥(Submo
dule.baseChange S (𝒜 0))) (TensorProduct R S A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma algebraMap_apply (x : (𝒜 0).baseChange S) : algebraMap _ (S ⊗[R] A) x = x := rfl

end Algebra

section Ring
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring ((𝒜 0).baseChange S) :=
  GradeZero.instRing fun i ↦ (𝒜 i).baseChange S

end Ring

section CommRing
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-
**GradedAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing ((𝒜 0).baseChange S) :=
  GradeZero.instCommRing fun i ↦ (𝒜 i).baseChange S

end CommRing

end GradedAlgebra

namespace GradedAlgHom

section liftEquiv

variable {ι R S A B : Type*}
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule S B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [Algebra R S] [Algebra R B] [IsScalarTower R S B]

open TensorProduct

/-- A map from the base change of a graded algebra is the same as a map to the scalar restriction.

In category-theoretical terms, this is an adjunction between:
1. `𝒜 ↦ (𝒜 · |>.baseChange S)`, a functor from Graded `R`-Algebra to Graded `S`-Algebra; and:
2. `ℬ ↦ (ℬ · |>.restrictScalars R)`, a functor from Graded `S`-Algebra to Graded `R`-Algebra.
-/
/-
**GradedAlgHom.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：liftEquiv : (𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S
) ->ₐᵍ[S] ℬ) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A map from the base change of a graded algebra is the same as a map to the scala
r restriction.

In category-theoretical terms, this is an adjunction between:
1. `𝒜 ↦ (𝒜 · |>.baseChange S)`, a functor from Graded `R`-Algebra to Graded `S`-
Algebra; and:
2. `ℬ ↦ (ℬ · |>.restrictScalars R)`, a functor from Graded `S`-Algebra to Graded
 `R`-Algebra.
-/
def liftEquiv : (𝒜 →ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S) →ₐᵍ[S] ℬ) where
  toFun f :=
    { AlgHom.liftEquiv R S A B f with
      map_mem hx := by
        obtain ⟨x, rfl⟩ := toBaseChange_surjective' _ _ hx
        induction x with
        | zero => simp
        | add => simp_all [add_mem]
        | tmul r x => simpa using smul_mem _ _ <| by exact f.map_mem x.2 }
  invFun f :=
    { AlgHom.liftEquiv R S A B |>.symm f with
      map_mem hx := f.map_mem <| tmul_mem_baseChange_of_mem _ hx }
  left_inv f := coe_toAlgHom_injective <| by simp
  right_inv f := coe_toAlgHom_injective <| by simp

variable {𝒜 ℬ}
/-
**GradedAlgHom.liftEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} {A : Type u_4} {B : Type u_
5} [inst : DecidableEq ι]   [inst_1 : AddMonoid ι] [inst_2 : CommSemiring R] [in
st_3 : CommSemiring S] [inst_4 : Semiring A] [inst_5 : Semiring B]   [inst_6 : A
lgebra R A] [inst_7 : Algebra S B] {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule S 
B}   [inst_8 : GradedAlgebra 𝒜] [inst_9 : GradedAlgebra ℬ] [inst_10 : Algebra R 
S] [inst_11 : Algebra R B]   [inst_12 : IsScalarTower R S B] (f : 𝒜 →ₐᵍ[R] fun x
 => Submodule.restrictScalars R (ℬ x)) (r : S) (x : A),   ((GradedAlgHom.liftEqu
iv 𝒜 ℬ) f) (r ⊗ₜ[R] x) = r • f x
参数：f : 𝒜 →ₐᵍ[R] fun x => Submodule.restrictScalars R (ℬ x)；r : S；x : A；(GradedAl
gHom.liftEquiv 𝒜 ℬ) f；r ⊗ₜ[R] x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma liftEquiv_tmul (f : 𝒜 →ₐᵍ[R] (ℬ · |>.restrictScalars R)) (r : S) (x : A) :
    liftEquiv 𝒜 ℬ f (r ⊗ₜ[R] x) = r • f x := rfl
/-
**GradedAlgHom.liftEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} {A : Type u_4} {B : Type u_
5} [inst : DecidableEq ι]   [inst_1 : AddMonoid ι] [inst_2 : CommSemiring R] [in
st_3 : CommSemiring S] [inst_4 : Semiring A] [inst_5 : Semiring B]   [inst_6 : A
lgebra R A] [inst_7 : Algebra S B] {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule S 
B}   [inst_8 : GradedAlgebra 𝒜] [inst_9 : GradedAlgebra ℬ] [inst_10 : Algebra R 
S] [inst_11 : Algebra R B]   [inst_12 : IsScalarTower R S B] (f : (fun x => Subm
odule.baseChange S (𝒜 x)) →ₐᵍ[S] ℬ) (x : A),   ((GradedAlgHom.liftEquiv 𝒜 ℬ).sym
m f) x = f (1 ⊗ₜ[R] x)
参数：f : (fun x => Submodule.baseChange S (𝒜 x)) →ₐᵍ[S] ℬ；x : A；(GradedAlgHom.lift
Equiv 𝒜 ℬ).symm f；1 ⊗ₜ[R] x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma liftEquiv_symm_apply (f : (𝒜 · |>.baseChange S) →ₐᵍ[S] ℬ) (x : A) :
    (liftEquiv 𝒜 ℬ).symm f x = f (1 ⊗ₜ[R] x) := rfl

variable (S 𝒜)

/-- Graded version of  `Algebra.TensorProduct.includeRight`, i.e. the inclusion from a graded
`R`-algebra `𝒜` to its base change to `S` and then restricted back to `R`. (The restriction does
not change the actual sets).

In categorical terms, this is the unit of the adjunction `GradedAlgHom.liftEquiv`. -/
/-
**GradedAlgHom.includeRight** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：includeRight : 𝒜 ->ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where 
__
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graded version of  `Algebra.TensorProduct.includeRight`, i.e. the inclusion from
 a graded
`R`-algebra `𝒜` to its base change to `S` and then restricted back to `R`. (The 
restriction does
not change the actual sets).

In categorical terms, this is the unit of the adjunction `GradedAlgHom.liftEquiv
`.
-/
def includeRight : 𝒜 →ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where
  __ := Algebra.TensorProduct.includeRight
  map_mem hx := tmul_mem_baseChange_of_mem _ hx

variable {𝒜}
/-
**GradedAlgHom.includeRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} (S : Type u_3) {A : Type u_4} [inst : Deci
dableEq ι] [inst_1 : AddMonoid ι]   [inst_2 : CommSemiring R] [inst_3 : CommSemi
ring S] [inst_4 : Semiring A] [inst_5 : Algebra R A]   {𝒜 : ι → Submodule R A} [
inst_6 : GradedAlgebra 𝒜] [inst_7 : Algebra R S] (x : A),   (GradedAlgHom.includ
eRight S 𝒜) x = 1 ⊗ₜ[R] x
参数：S : Type u_3；x : A；GradedAlgHom.includeRight S 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma includeRight_apply (x : A) : includeRight S 𝒜 x = 1 ⊗ₜ[R] x := rfl

end liftEquiv

end GradedAlgHom

