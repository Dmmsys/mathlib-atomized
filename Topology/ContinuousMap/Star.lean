/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Topology.Algebra.Star
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Star structures on continuous maps.

-/

@[expose] public section

namespace ContinuousMap

/-!
### Star structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/


section StarStructure

variable {R α β : Type*}
variable [TopologicalSpace α] [TopologicalSpace β]

section Star

variable [Star β] [ContinuousStar β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star C(α, β)
  body: starContinuousMap.comp f

@[simp]

中文:
实例 :
  签名: 对合 C(α, β)
  定义体: starContinuousMap.comp f

@[simp]

Depends on / 依赖: starContinuousMap, starContinuousMap.comp
-/
instance : Star C(α, β) where star f := starContinuousMap.comp f

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (f : C(α, β))
  statement: ⇑(star f) = star (⇑f)
  proof: rfl

@[simp]

中文:
定理 coe_star
  条件: (f : C(α, β))
  结论: ⇑(star f) = star (⇑f)
  证明: rfl

@[simp]
-/
theorem coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

@[simp]
/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: (f : C(α, β)) (x : α)
  statement: star f x = star (f x)
  proof: rfl

中文:
定理 star_apply
  条件: (f : C(α, β)) (x : α)
  结论: star f x = star (f x)
  证明: rfl
-/
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl

/--
Instance `instTrivialStar` / 实例 `instTrivialStar`

English:
instance instTrivialStar
  signature: [TrivialStar β]
  body: ext fun _ => star_trivial _

中文:
实例 instTrivialStar
  签名: [TrivialStar β]
  定义体: ext fun _ => star_trivial _

Depends on / 依赖: star_trivial
-/
instance instTrivialStar [TrivialStar β] : TrivialStar C(α, β) where
  star_trivial _ := ext fun _ => star_trivial _

end Star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: β] [ContinuousStar β] : InvolutiveStar C(α, β) where
  body: ext fun _ => star_star _

中文:
实例 [InvolutiveStar
  签名: β] [余ntinuousStar β] : InvolutiveStar C(α, β) where
  定义体: ext fun _ => star_star _

Depends on / 依赖: star_star
-/
instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β) where
  star_involutive _ := ext fun _ => star_star _

/--
Instance `starAddMonoid` / 实例 `starAddMonoid`

English:
instance starAddMonoid
  signature: [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β]
  body: ext fun _ => star_add _ _

中文:
实例 starAddMonoid
  签名: [加法幺半群 β] [连续加法 β] [StarAdd幺半群 β] [余ntinuousStar β]
  定义体: ext fun _ => star_add _ _

Depends on / 依赖: star_add
-/
instance starAddMonoid [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where
  star_add _ _ := ext fun _ => star_add _ _

/--
Instance `starMul` / 实例 `starMul`

English:
instance starMul
  signature: [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β]
  body: ext fun _ => star_mul _ _

中文:
实例 starMul
  签名: [乘法 β] [连续乘法 β] [StarMul β] [余ntinuousStar β]
  定义体: ext fun _ => star_mul _ _

Depends on / 依赖: star_mul
-/
instance starMul [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β] :
    StarMul C(α, β) where
  star_mul _ _ := ext fun _ => star_mul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: β] [IsTopologicalSemiring β] [StarRing β] [ContinuousStar β] :
  body: { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }

中文:
实例 [非幺非结合半环
  签名: β] [是TopologicalSemiring β] [对合环 β] [余ntinuousStar β] :
  定义体: { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }

Depends on / 依赖: ContinuousMap, ContinuousMap.starAddMonoid, ContinuousMap.starMul, starAddMonoid, starMul
-/
instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
  body: ext fun _ => star_smul _ _

中文:
实例 [对合
  签名: R] [对合 β] [标量乘法 R β] [对合模 R β] [余ntinuousStar β]
  定义体: ext fun _ => star_smul _ _

Depends on / 依赖: star_smul
-/
instance [Star R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
    [ContinuousConstSMul R β] : StarModule R C(α, β) where
  star_smul _ _ := ext fun _ => star_smul _ _

end StarStructure

section Precomposition

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]

/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `ContinuousMap.compMonoidHom'` and
`ContinuousMap.compAddMonoidHom'`, `ContinuousMap.compRightAlgHom` for bundlings of
pre-composition into a `MonoidHom`, an `AddMonoidHom` and an `AlgHom`, respectively, under
suitable assumptions on `A`. -/
@[simps]
/--
Definition of `compStarAlgHom'` / `compStarAlgHom'` 的定义

English:
definition compStarAlgHom'
  signature: (f : C(X, Y))
  body: g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

中文:
定义 compStarAlgHom'
  签名: (f : C(X, Y))
  定义体: g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

Depends on / 依赖: g.comp
-/
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) ->⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/--
theorem `compStarAlgHom'_id` / 定理 `compStarAlgHom'_id`

English:
theorem compStarAlgHom'_id
  statement: compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A)
  proof: StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

中文:
定理 compStarAlgHom'_id
  结论: compStarAlgHom' 𝕜 A (连续映射.id X) = StarAlg态射.id 𝕜 C(X, A)
  证明: StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
-/
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

/--
theorem `compStarAlgHom'_comp` / 定理 `compStarAlgHom'_comp`

English:
theorem compStarAlgHom'_comp
  given: (g : C(Y, Z)) (f : C(X, Y))
  proof: StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

中文:
定理 compStarAlgHom'_comp
  条件: (g : C(Y, Z)) (f : C(X, Y))
  证明: StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
-/
theorem compStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compStarAlgHom' 𝕜 A (g.comp f) = (compStarAlgHom' 𝕜 A f).comp (compStarAlgHom' 𝕜 A g) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

end Precomposition

section Postcomposition

variable (X : Type*) {𝕜 A B C : Type*} [TopologicalSpace X] [CommSemiring 𝕜]
variable [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]
variable [TopologicalSpace B] [Semiring B] [IsTopologicalSemiring B] [Star B]
variable [ContinuousStar B] [Algebra 𝕜 B]
variable [TopologicalSpace C] [Semiring C] [IsTopologicalSemiring C] [Star C]
variable [ContinuousStar C] [Algebra 𝕜 C]

/-- Post-composition with a continuous star algebra homomorphism is a star algebra homomorphism
between spaces of continuous maps. -/
@[simps]
/--
Definition of `compStarAlgHom` / `compStarAlgHom` 的定义

English:
definition compStarAlgHom
  signature: (φ : A ->⋆ₐ[𝕜] B) (hφ : Continuous φ)
  body: (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_s

中文:
定义 compStarAlgHom
  签名: (φ : A ->⋆ₐ[𝕜] B) (hφ : 连续 φ)
  定义体: (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_s
-/
def compStarAlgHom (φ : A ->⋆ₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) ->⋆ₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_star φ (f x)

/--
lemma `compStarAlgHom_id` / 引理 `compStarAlgHom_id`

English:
lemma compStarAlgHom_id
  statement: compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A)
  proof: rfl

中文:
引理 compStarAlgHom_id
  结论: compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A)
  证明: rfl
-/
lemma compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) := rfl

/--
lemma `compStarAlgHom_comp` / 引理 `compStarAlgHom_comp`

English:
lemma compStarAlgHom_comp
  statement: (φ : A ->⋆ₐ[𝕜] B) (ψ : B ->⋆ₐ[𝕜] C) (hφ : Continuous φ)
  proof: rfl

中文:
引理 compStarAlgHom_comp
  结论: (φ : A ->⋆ₐ[𝕜] B) (ψ : B ->⋆ₐ[𝕜] C) (hφ : 连续 φ)
  证明: rfl
-/
lemma compStarAlgHom_comp (φ : A ->⋆ₐ[𝕜] B) (ψ : B ->⋆ₐ[𝕜] C) (hφ : Continuous φ)
    (hψ : Continuous ψ) : compStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compStarAlgHom X ψ hψ).comp (compStarAlgHom X φ hφ) :=
  rfl

end Postcomposition

end ContinuousMap

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [StarRing A]
variable [ContinuousStar A] [Algebra 𝕜 A]

/-- `ContinuousMap.compStarAlgHom'` as a `StarAlgEquiv` when the continuous map `f` is
actually a homeomorphism. -/
@[simps]
/--
Definition of `compStarAlgEquiv'` / `compStarAlgEquiv'` 的定义

English:
definition compStarAlgEquiv'
  signature: (f : X ≃ₜ Y)
  body: { (f : C(X, Y)).compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.co

中文:
定义 compStarAlgEquiv'
  签名: (f : X ≃ₜ Y)
  定义体: { (f : C(X, Y)).compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.co

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, ContinuousMap.comp_assoc, ContinuousMap.comp_id, _apply, compStarAlgHom, comp_assoc, comp_id, f.symm, invFun, left_inv, map_smul, right_inv, symm_comp_toContinuousMap, toContinuousMap_comp_symm
-/
def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  { (f : C(X, Y)).compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_toContinuousMap, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul ((f : C(X, Y)).compStarAlgHom' 𝕜 A) k a }

end Homeomorph

/-! ### Evaluation as a bundled map -/

variable {X : Type*} (S R : Type*) [TopologicalSpace X] [CommSemiring S] [CommSemiring R]
variable [Algebra S R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Evaluation of continuous maps at a point, bundled as a star algebra homomorphism. -/
@[simps!]
/--
Definition of `ContinuousMap.evalStarAlgHom` / `ContinuousMap.evalStarAlgHom` 的定义

English:
definition ContinuousMap.evalStarAlgHom
  signature: [StarRing R] [ContinuousStar R] (x : X)
  body: { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }

中文:
定义 连续映射.evalStarAlgHom
  签名: [对合环 R] [余ntinuousStar R] (x : X)
  定义体: { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }

Depends on / 依赖: ContinuousMap, ContinuousMap.evalAlgHom, evalAlgHom, map_star
-/
def ContinuousMap.evalStarAlgHom [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) ->⋆ₐ[S] R :=
  { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }
