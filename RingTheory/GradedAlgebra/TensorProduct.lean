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
variable [Semiring A] [Algebra R A] (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: : GradedAlgebra fun i => (𝒜 i).baseChange S where
  body: tmul_mem_baseChange_of_mem _ one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S otimes[R] A)) ((𝒜 j).baseChange S) <=
      (𝒜 (i + j)).baseChange S from fun xi xj => (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le,

中文:
实例 baseChange
  签名: : 分次代数 fun i => (𝒜 i).baseChange S where
  定义体: tmul_mem_baseChange_of_mem _ one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S otimes[R] A)) ((𝒜 j).baseChange S) <=
      (𝒜 (i + j)).baseChange S from fun xi xj => (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le,

Depends on / 依赖: one_mem_graded, tmul_mem_baseChange_of_mem
-/
instance baseChange : GradedAlgebra fun i => (𝒜 i).baseChange S where
one_mem := tmul_mem_baseChange_of_mem _ one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S otimes[R] A)) ((𝒜 j).baseChange S) <=
      (𝒜 (i + j)).baseChange S from fun xi xj => (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le, Set.image2_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
simpa using subset_span Set.mem_image_of_mem _ mul_mem_graded hx hy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring ((𝒜 0).baseChange S)
  body: GradeZero.instSemiring fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 半环 ((𝒜 0).baseChange S)
  定义体: GradeZero.instSemiring fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instSemiring, baseChange, instSemiring
-/
instance : Semiring ((𝒜 0).baseChange S) :=
  GradeZero.instSemiring fun i => (𝒜 i).baseChange S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra S ((𝒜 0).baseChange S)
  body: GradeZero.instAlgebra fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 代数 S ((𝒜 0).baseChange S)
  定义体: GradeZero.instAlgebra fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instAlgebra, baseChange, instAlgebra
-/
instance : Algebra S ((𝒜 0).baseChange S) :=
  GradeZero.instAlgebra fun i => (𝒜 i).baseChange S

/--
lemma `coe_algebraMap_apply` / 引理 `coe_algebraMap_apply`

English:
lemma coe_algebraMap_apply
  given: (s : S)
  proof: rfl

中文:
引理 coe_algebraMap_apply
  条件: (s : S)
  证明: rfl
-/
@[simp] lemma coe_algebraMap_apply (s : S) :
    (algebraMap _ ((𝒜 0).baseChange S) s : S otimes[R] A) = s otimesₜ 1 := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring ((𝒜 0).baseChange S)
  body: GradeZero.instCommSemiring fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 交换半环 ((𝒜 0).baseChange S)
  定义体: GradeZero.instCommSemiring fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instCommSemiring, baseChange, instCommSemiring
-/
instance : CommSemiring ((𝒜 0).baseChange S) :=
  GradeZero.instCommSemiring fun i => (𝒜 i).baseChange S

end CommSemiring

section Algebra
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra ((𝒜 0).baseChange S) (S otimes[R] A)
  body: GradeZero.instAlgebraSubtypeMemOfNat fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 代数 ((𝒜 0).baseChange S) (S otimes[R] A)
  定义体: GradeZero.instAlgebraSubtypeMemOfNat fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instAlgebraSubtypeMemOfNat, baseChange, instAlgebraSubtypeMemOfNat
-/
instance : Algebra ((𝒜 0).baseChange S) (S otimes[R] A) :=
  GradeZero.instAlgebraSubtypeMemOfNat fun i => (𝒜 i).baseChange S

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (x : (𝒜 0).baseChange S)
  statement: algebraMap _ (S otimes[R] A) x = x
  proof: rfl

中文:
引理 algebraMap_apply
  条件: (x : (𝒜 0).baseChange S)
  结论: algebraMap _ (S otimes[R] A) x = x
  证明: rfl
-/
@[simp] lemma algebraMap_apply (x : (𝒜 0).baseChange S) : algebraMap _ (S otimes[R] A) x = x := rfl

end Algebra

section Ring
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [Semiring A] [Algebra R A] (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring ((𝒜 0).baseChange S)
  body: GradeZero.instRing fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 环 ((𝒜 0).baseChange S)
  定义体: GradeZero.instRing fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instRing, baseChange, instRing
-/
instance : Ring ((𝒜 0).baseChange S) :=
  GradeZero.instRing fun i => (𝒜 i).baseChange S

end Ring

section CommRing
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing ((𝒜 0).baseChange S)
  body: GradeZero.instCommRing fun i => (𝒜 i).baseChange S

中文:
实例 :
  签名: 交换环 ((𝒜 0).baseChange S)
  定义体: GradeZero.instCommRing fun i => (𝒜 i).baseChange S

Depends on / 依赖: GradeZero, GradeZero.instCommRing, baseChange, instCommRing
-/
instance : CommRing ((𝒜 0).baseChange S) :=
  GradeZero.instCommRing fun i => (𝒜 i).baseChange S

end CommRing

end GradedAlgebra

namespace GradedAlgHom

section liftEquiv

variable {ι R S A B : Type*}
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable (𝒜 : ι -> Submodule R A) (ℬ : ι -> Submodule S B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [Algebra R S] [Algebra R B] [IsScalarTower R S B]

open TensorProduct

/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : (𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) where
  body: { AlgHom.liftEquiv R S A B f with
      map_mem hx := by
        obtain ⟨x, rfl⟩ := toBaseChange_surjective' _ _ hx
        induction x with
        | zero => simp
        | add => simp_all [add_mem]
| tmul r x => simpa using smul_mem _ _ by exact f.map_mem x.2 }
  invFun f :=
    { AlgHom.liftEquiv

中文:
定义 liftEquiv
  签名: : (𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) where
  定义体: { AlgHom.liftEquiv R S A B f with
      map_mem hx := by
        obtain ⟨x, rfl⟩ := toBaseChange_surjective' _ _ hx
        induction x with
        | zero => simp
        | add => simp_all [add_mem]
| tmul r x => simpa using smul_mem _ _ by exact f.map_mem x.2 }
  invFun f :=
    { AlgHom.liftEquiv

Depends on / 依赖: AlgHom, AlgHom.liftEquiv, add_mem, coe_toAlgHom_injective, f.map_mem, invFun, left_inv, liftEquiv, map_mem, right_inv, smul_mem, tmul_mem_baseChange_of_mem, toBaseChange_surjective
-/
def liftEquiv : (𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) where
  toFun f :=
    { AlgHom.liftEquiv R S A B f with
      map_mem hx := by
        obtain ⟨x, rfl⟩ := toBaseChange_surjective' _ _ hx
        induction x with
        | zero => simp
        | add => simp_all [add_mem]
| tmul r x => simpa using smul_mem _ _ by exact f.map_mem x.2 }
  invFun f :=
    { AlgHom.liftEquiv R S A B |>.symm f with
map_mem hx := f.map_mem tmul_mem_baseChange_of_mem _ hx }
left_inv f := coe_toAlgHom_injective by simp
right_inv f := coe_toAlgHom_injective by simp

variable {𝒜 ℬ}

/--
lemma `liftEquiv_tmul` / 引理 `liftEquiv_tmul`

English:
lemma liftEquiv_tmul
  given: (f : 𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) (r : S) (x : A)
  proof: rfl

中文:
引理 liftEquiv_tmul
  条件: (f : 𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) (r : S) (x : A)
  证明: rfl
-/
@[simp] lemma liftEquiv_tmul (f : 𝒜 ->ₐᵍ[R] (ℬ · |>.restrictScalars R)) (r : S) (x : A) :
    liftEquiv 𝒜 ℬ f (r otimesₜ[R] x) = r • f x := rfl

/--
lemma `liftEquiv_symm_apply` / 引理 `liftEquiv_symm_apply`

English:
lemma liftEquiv_symm_apply
  given: (f : (𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) (x : A)
  proof: rfl

中文:
引理 liftEquiv_symm_apply
  条件: (f : (𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) (x : A)
  证明: rfl
-/
@[simp] lemma liftEquiv_symm_apply (f : (𝒜 · |>.baseChange S) ->ₐᵍ[S] ℬ) (x : A) :
    (liftEquiv 𝒜 ℬ).symm f x = f (1 otimesₜ[R] x) := rfl

variable (S 𝒜)

/--
Definition of `includeRight` / `includeRight` 的定义

English:
definition includeRight
  signature: : 𝒜 ->ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where
  body: Algebra.TensorProduct.includeRight
  map_mem hx := tmul_mem_baseChange_of_mem _ hx

中文:
定义 includeRight
  签名: : 𝒜 ->ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where
  定义体: Algebra.TensorProduct.includeRight
  map_mem hx := tmul_mem_baseChange_of_mem _ hx

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, TensorProduct, includeRight
-/
def includeRight : 𝒜 ->ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where
  __ := Algebra.TensorProduct.includeRight
  map_mem hx := tmul_mem_baseChange_of_mem _ hx

variable {𝒜}

/--
lemma `includeRight_apply` / 引理 `includeRight_apply`

English:
lemma includeRight_apply
  given: (x : A)
  statement: includeRight S 𝒜 x = 1 otimesₜ[R] x
  proof: rfl

中文:
引理 includeRight_apply
  条件: (x : A)
  结论: includeRight S 𝒜 x = 1 otimesₜ[R] x
  证明: rfl
-/
@[simp] lemma includeRight_apply (x : A) : includeRight S 𝒜 x = 1 otimesₜ[R] x := rfl

end liftEquiv

end GradedAlgHom
