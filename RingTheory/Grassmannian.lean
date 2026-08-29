/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined
  to be the set of submodules of `M` whose **quotient** is locally free of rank `k`. Note that there
  is another convention in literature where the `k`ᵗʰ Grassmannian would instead be `k`-dimensional
  subspaces of a given vector space over a field. See implementation notes below.

- `Module.Grassmannian.functor`: The Grassmannian functor that sends an `R`-algebra `A` to the set
  `G(k, A ⊗[R] M; A)`.

## Implementation notes

In the literature, two conventions exist:

1. The `k`ᵗʰ Grassmannian parametrises `k`-dimensional **subspaces** of a given finite-dimensional
   vector space over a field.
2. The `k`ᵗʰ Grassmannian parametrises **quotients** that are locally free of rank `k`, of a given
   module over a ring.

For the purposes of Algebraic Geometry, the first definition here cannot be generalised to obtain
a scheme to represent the functor, which is why the second definition is the one chosen by
[Grothendieck, EGA I.9.7.3][grothendieck-1971] (Springer edition only), and in EGA V.11
(unpublished).

The first definition in the stated generality (i.e. over a field `F`, and finite-dimensional vector
space `V`) can be recovered from the second definition by noting that `k`-dimensional subspaces of
`V` are canonically equivalent to `(n-k)`-dimensional quotients of `V`, and also to `k`-dimensional
quotients of `V*`, the dual of `V`. In symbols, this means that the first definition is equivalent
to `G(n - k, V; F)` and also to `G(k, V →ₗ[F] F; F)`, where `n` is the dimension of `V`.

## TODO
- Define and recover the subspace-definition (i.e. the first definition above).
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Module.Grassmannian.functor`. This
  will correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Module.Grassmannian.functor R M k`.
-/

public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : Nat)

/--
Definition of `Grassmannian` / `Grassmannian` 的定义

English:
structure Grassmannian
  parameters: extends Submodule R M
  extends: Submodule R M
  axioms and operations (3):
    - finite_quotient : Module.Finite R (M ⧸ toSubmodule)
    - projective_quotient : Projective R (M ⧸ toSubmodule)
    - rankAtStalk_eq : forall p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

中文:
结构 Grassmann流形
  参数: extends 子模 R M
  继承: 子模 R M
  公理与运算 (3 个):
    - finite_quotient : 模.有限 R (M ⧸ toSubmodule)
    - projective_quotient : 投射 R (M ⧸ toSubmodule)
    - rankAtStalk_eq : 对任意 p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k
-/
@[stacks 089R] structure Grassmannian extends Submodule R M where
  finite_quotient : Module.Finite R (M ⧸ toSubmodule)
  projective_quotient : Projective R (M ⧸ toSubmodule)
  rankAtStalk_eq : forall p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

attribute [instance] Grassmannian.finite_quotient Grassmannian.projective_quotient

namespace Grassmannian

@[inherit_doc] scoped notation "G(" k ", " M "; " R ")" => Grassmannian R M k

variable {R M k}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut G(k, M; R) (Submodule R M)
  body: ⟨toSubmodule⟩

中文:
实例 :
  签名: CoeOut G(k, M; R) (子模 R M)
  定义体: ⟨toSubmodule⟩

Depends on / 依赖: toSubmodule
-/
instance : CoeOut G(k, M; R) (Submodule R M) :=
  ⟨toSubmodule⟩

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂)
  statement: N₁ = N₂
  proof: by
  cases N₁; cases N₂; congr 1

中文:
引理 ext
  条件: {N₁ N₂ : G(k, M; R)} (h : (N₁ : 子模 R M) = N₂)
  结论: N₁ = N₂
  证明: by
  cases N₁; cases N₂; congr 1
-/
@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
  cases N₁; cases N₂; congr 1

section Functor

open CategoryTheory TensorProduct AlgebraTensorModule

attribute [local ext high] ConcreteCategory.hom_ext

variable {A : Type w} [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra R B]

section BaseChangeMkQ

variable [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A otimes[R] M))

/--
Definition of `baseChangeMkQ` / `baseChangeMkQ` 的定义

English:
definition baseChangeMkQ
  signature: : B otimes[R] M ->ₗ[B] B otimes[A] ((A otimes[R] M) ⧸ N)
  body: N.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap

中文:
定义 baseChangeMkQ
  签名: : B otimes[R] M ->ₗ[B] B otimes[A] ((A otimes[R] M) ⧸ N)
  定义体: N.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap

Depends on / 依赖: N.mkQ.baseChange, baseChange, cancelBaseChange, symm.toLinearMap, toLinearMap
-/
def baseChangeMkQ : B otimes[R] M ->ₗ[B] B otimes[A] ((A otimes[R] M) ⧸ N) :=
  N.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap

variable {B}

/--
theorem `baseChangeMkQ_surjective` / 定理 `baseChangeMkQ_surjective`

English:
theorem baseChangeMkQ_surjective
  statement: Function.Surjective (baseChangeMkQ B N)
  proof: (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
    (cancelBaseChange R A B B M).symm.surjective

中文:
定理 baseChangeMkQ_surjective
  结论: 函数.满射 (baseChangeMkQ B N)
  证明: (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
    (cancelBaseChange R A B B M).symm.surjective

Depends on / 依赖: LinearMap, LinearMap.baseChange_surjective, Submodule, Submodule.mkQ_surjective, baseChange_surjective, cancelBaseChange, mkQ_surjective, surjective, symm.surjective
-/
theorem baseChangeMkQ_surjective : Function.Surjective (baseChangeMkQ B N) :=
  (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
    (cancelBaseChange R A B B M).symm.surjective

/--
Definition of `baseChangeMkQEquiv` / `baseChangeMkQEquiv` 的定义

English:
definition baseChangeMkQEquiv
  body: (baseChangeMkQ B N).quotKerEquivOfSurjective (baseChangeMkQ_surjective N)

中文:
定义 baseChangeMkQEquiv
  定义体: (baseChangeMkQ B N).quotKerEquivOfSurjective (baseChangeMkQ_surjective N)

Depends on / 依赖: baseChangeMkQ, baseChangeMkQ_surjective, quotKerEquivOfSurjective
-/
noncomputable def baseChangeMkQEquiv :=
  (baseChangeMkQ B N).quotKerEquivOfSurjective (baseChangeMkQ_surjective N)

end BaseChangeMkQ

variable {B} (f : A ->ₐ[R] B)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (N : G(k, (A otimes[R] M); A))
  body: letI : Algebra A B := f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  haveI equiv := baseChangeMkQEquiv N.toSubmodule
  { toSubmodule := (baseChangeMkQ B N.toSubmodule).ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B otimes[A] ((A otimes[R] M) ⧸ N.toSubmodule)) p := by
simpa using congrArg (fun g => g p) Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A otimes[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }

中文:
定义 map
  签名: (N : G(k, (A otimes[R] M); A))
  定义体: letI : Algebra A B := f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  haveI equiv := baseChangeMkQEquiv N.toSubmodule
  { toSubmodule := (baseChangeMkQ B N.toSubmodule).ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B otimes[A] ((A otimes[R] M) ⧸ N.toSubmodule)) p := by
simpa using congrArg (fun g => g p) Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A otimes[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }

Depends on / 依赖: Algebra, Finite, IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, Module, Module.Finite.equiv, Module.Projective.of_equiv, Module.rankAt, N.toSubmodule, Projective, algebraMap_eq, baseChangeMkQ, baseChangeMkQEquiv, equiv.symm, f.toAlgebra, finite_quotient, of_algebraMap_eq, of_equiv, otimes
-/
def map (N : G(k, (A otimes[R] M); A)) : G(k, (B otimes[R] M); B) :=
  letI : Algebra A B := f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  haveI equiv := baseChangeMkQEquiv N.toSubmodule
  { toSubmodule := (baseChangeMkQ B N.toSubmodule).ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B otimes[A] ((A otimes[R] M) ⧸ N.toSubmodule)) p := by
simpa using congrArg (fun g => g p) Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A otimes[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }

/--
theorem `map_toSubmodule` / 定理 `map_toSubmodule`

English:
theorem map_toSubmodule
  given: (N : G(k, A otimes[R] M; A))
  proof: f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  (map f N).toSubmodule = (baseChangeMkQ B N.toSubmodule).ker := by rfl

中文:
定理 map_toSubmodule
  条件: (N : G(k, A otimes[R] M; A))
  证明: f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  (map f N).toSubmodule = (baseChangeMkQ B N.toSubmodule).ker := by rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
theorem map_toSubmodule (N : G(k, A otimes[R] M; A)) :
  letI : Algebra A B := f.toAlgebra
letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' IsScalarTower.algebraMap_eq R A B
  (map f N).toSubmodule = (baseChangeMkQ B N.toSubmodule).ker := by rfl

variable (k)

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (A : CommAlgCat R) (N : G(k, A otimes[R] M; A))
  proof: by
  ext : 1
  exact (ker_baseChange_comp_cancelBaseChange_symm N.mkQ).trans N.toSubmodule.ker_mkQ

中文:
定理 map_id
  条件: (A : 交换Alg范畴 R) (N : G(k, A otimes[R] M; A))
  证明: by
  ext : 1
  exact (ker_baseChange_comp_cancelBaseChange_symm N.mkQ).trans N.toSubmodule.ker_mkQ
-/
@[simp] theorem map_id (A : CommAlgCat R) (N : G(k, A otimes[R] M; A)) :
    map (.id R A) N = N := by
  ext : 1
  exact (ker_baseChange_comp_cancelBaseChange_symm N.mkQ).trans N.toSubmodule.ker_mkQ

variable {C : Type w} [CommRing C] [Algebra R C]
variable (g : B ->ₐ[R] C)

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (N : G(k, A otimes[R] M; A))
  proof: by
  algebraize [f.toRingHom, g.toRingHom, (g.comp f).toRingHom]
  -- FIXME: `algebraize` doesn't generate this instance, even though it seems like it should
  let : IsScalarTower A B C := by apply IsScalarTower.of_algebraMap_eq'; rfl
  let fAB := baseChangeMkQ B N.toSubmodule
  let fAC := baseChangeMkQ C N.toSubmodule
  let fBC := baseChangeMkQ C fAB.ker
  have hfAB : Function.Surjective fAB :=
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  let e := (fAB.quotKerEquivOfSurjective hfAB).baseChange B C ≪≫ₗ
    cancelBaseChange A B C C (A otimes[R] M ⧸ N.toSubmodule)
  ext x
  have hfAC_ker_eq : (map (g.comp f) N).toSubmodule = fAC.ker := map_toSubmodule (g.comp f) N
  have hfBC_ker_eq : (map g (map f N)).toSubmodule = fBC.ker := by
    rw [map_toSubmodule g (map f N)]; rw [map_toSubmodule f N]
  have hcomp : fAC = e.toLinearMap.comp fBC := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [fAC, fBC, e]
    | tmul c m =>
      simp only [fAC, fBC, e, baseChangeMkQ, LinearMap.comp_apply, cancelBaseChange_symm_tmul,
         LinearMap.baseChange_tmul, Submodule.mkQ_apply, LinearEquiv.coe_trans, LinearEquiv.coe_coe,
         LinearEquiv.coe_baseChange, LinearMap.quotKerEquivOfSurjective_apply_mk]
      simp [fAB, baseChangeMkQ]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at *
      rw [hx]; rw [hy]
  rw [hfAC_ker_eq]; rw [hfBC_ker_eq]; rw [hcomp]; rw [LinearEquiv.ker_comp]

中文:
定理 map_comp
  条件: (N : G(k, A otimes[R] M; A))
  证明: by
  algebraize [f.toRingHom, g.toRingHom, (g.comp f).toRingHom]
  -- FIXME: `algebraize` doesn't generate this instance, even though it seems like it should
  let : IsScalarTower A B C := by apply IsScalarTower.of_algebraMap_eq'; rfl
  let fAB := baseChangeMkQ B N.toSubmodule
  let fAC := baseChangeMkQ C N.toSubmodule
  let fBC := baseChangeMkQ C fAB.ker
  have hfAB : Function.Surjective fAB :=
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  let e := (fAB.quotKerEquivOfSurjective hfAB).baseChange B C ≪≫ₗ
    cancelBaseChange A B C C (A otimes[R] M ⧸ N.toSubmodule)
  ext x
  have hfAC_ker_eq : (map (g.comp f) N).toSubmodule = fAC.ker := map_toSubmodule (g.comp f) N
  have hfBC_ker_eq : (map g (map f N)).toSubmodule = fBC.ker := by
    rw [map_toSubmodule g (map f N)]; rw [map_toSubmodule f N]
  have hcomp : fAC = e.toLinearMap.comp fBC := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [fAC, fBC, e]
    | tmul c m =>
      simp only [fAC, fBC, e, baseChangeMkQ, LinearMap.comp_apply, cancelBaseChange_symm_tmul,
         LinearMap.baseChange_tmul, Submodule.mkQ_apply, LinearEquiv.coe_trans, LinearEquiv.coe_coe,
         LinearEquiv.coe_baseChange, LinearMap.quotKerEquivOfSurjective_apply_mk]
      simp [fAB, baseChangeMkQ]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at *
      rw [hx]; rw [hy]
  rw [hfAC_ker_eq]; rw [hfBC_ker_eq]; rw [hcomp]; rw [LinearEquiv.ker_comp]

Depends on / 依赖: algebraize, f.toRingHom, g.comp, g.toRingHom, toRingHom
-/
theorem map_comp (N : G(k, A otimes[R] M; A)) :
    map (g.comp f) N = map g (map f N) := by
  algebraize [f.toRingHom, g.toRingHom, (g.comp f).toRingHom]
  -- FIXME: `algebraize` doesn't generate this instance, even though it seems like it should
  let : IsScalarTower A B C := by apply IsScalarTower.of_algebraMap_eq'; rfl
  let fAB := baseChangeMkQ B N.toSubmodule
  let fAC := baseChangeMkQ C N.toSubmodule
  let fBC := baseChangeMkQ C fAB.ker
  have hfAB : Function.Surjective fAB :=
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  let e := (fAB.quotKerEquivOfSurjective hfAB).baseChange B C ≪≫ₗ
    cancelBaseChange A B C C (A otimes[R] M ⧸ N.toSubmodule)
  ext x
  have hfAC_ker_eq : (map (g.comp f) N).toSubmodule = fAC.ker := map_toSubmodule (g.comp f) N
  have hfBC_ker_eq : (map g (map f N)).toSubmodule = fBC.ker := by
    rw [map_toSubmodule g (map f N)]; rw [map_toSubmodule f N]
  have hcomp : fAC = e.toLinearMap.comp fBC := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [fAC, fBC, e]
    | tmul c m =>
      simp only [fAC, fBC, e, baseChangeMkQ, LinearMap.comp_apply, cancelBaseChange_symm_tmul,
         LinearMap.baseChange_tmul, Submodule.mkQ_apply, LinearEquiv.coe_trans, LinearEquiv.coe_coe,
         LinearEquiv.coe_baseChange, LinearMap.quotKerEquivOfSurjective_apply_mk]
      simp [fAB, baseChangeMkQ]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at *
      rw [hx]; rw [hy]
  rw [hfAC_ker_eq]; rw [hfBC_ker_eq]; rw [hcomp]; rw [LinearEquiv.ker_comp]

/-- The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`. -/
@[expose, simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  body: G(k, (A otimes[R] M); A)
  map f := ↾map f.hom
  map_id A := by ext N : 1; exact map_id k A N
  map_comp f g := by ext N : 1; exact map_comp k f.hom g.hom N

中文:
定义 functor
  签名: : 交换Alg范畴.{w, u} R ⥤ 类型 (最大值 v w) where
  定义体: G(k, (A otimes[R] M); A)
  map f := ↾map f.hom
  map_id A := by ext N : 1; exact map_id k A N
  map_comp f g := by ext N : 1; exact map_comp k f.hom g.hom N

Depends on / 依赖: otimes
-/
def functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := G(k, (A otimes[R] M); A)
  map f := ↾map f.hom
  map_id A := by ext N : 1; exact map_id k A N
  map_comp f g := by ext N : 1; exact map_comp k f.hom g.hom N

end Functor

end Grassmannian

end Module
