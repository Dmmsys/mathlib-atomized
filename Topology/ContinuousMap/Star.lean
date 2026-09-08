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

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star C(α, β) where star f := starContinuousMap.comp f

@[simp]
/-
**ContinuousMap.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f)
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

@[simp]
/-
**ContinuousMap.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：star_apply (f : C(α, β)) (x : α) : star f x = star (f x)
参数：f : C(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl
/-
**ContinuousMap.instTrivialStar** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instTrivialStar [TrivialStar β] : TrivialStar C(α, β) where star_trivial _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
-/
instance instTrivialStar [TrivialStar β] : TrivialStar C(α, β) where
  star_trivial _ := ext fun _ => star_trivial _

end Star

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β) where
  star_involutive _ := ext fun _ => star_star _
/-
**ContinuousMap.starAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：starAddMonoid [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [Continuou
sStar β] : StarAddMonoid C(α, β) where star_add _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance starAddMonoid [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where
  star_add _ _ := ext fun _ => star_add _ _
/-
**ContinuousMap.starMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：starMul [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β] : StarMul
 C(α, β) where star_mul _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance starMul [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β] :
    StarMul C(α, β) where
  star_mul _ _ := ext fun _ => star_mul _ _
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**ContinuousMap.compStarAlgHom'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：compStarAlgHom' (f : C(X, Y)) : C(Y, A) ->⋆ₐ[𝕜] C(X, A) where toFun g
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre
-composition
with the continuous function `f`. See `ContinuousMap.compMonoidHom'` and
`ContinuousMap.compAddMonoidHom'`, `ContinuousMap.compRightAlgHom` for bundlings
 of
pre-composition into a `MonoidHom`, an `AddMonoidHom` and an `AlgHom`, respectiv
ely, under
suitable assumptions on `A`.
-/
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- `ContinuousMap.compStarAlgHom'` sends the identity continuous map to the identity
`StarAlgHom` -/
/-
**ContinuousMap.compStarAlgHom'_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (𝕜 : Type u_4) [inst_1 : Comm
Semiring 𝕜] (A : Type u_5)   [inst_2 : TopologicalSpace A] [inst_3 : Semiring A]
 [inst_4 : IsTopologicalSemiring A] [inst_5 : Star A]   [inst_6 : ContinuousStar
 A] [inst_7 : Algebra 𝕜 A],   ContinuousMap.compStarAlgHom' 𝕜 A (ContinuousMap.i
d X) = StarAlgHom.id 𝕜 C(X, A)
参数：𝕜 : Type u_4；A : Type u_5；ContinuousMap.id X；X, A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g

--- 原说明 ---
`ContinuousMap.compStarAlgHom'` sends the identity continuous map to the identit
y
`StarAlgHom`
-/
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

/-- `ContinuousMap.compStarAlgHom'` is functorial. -/
/-
**ContinuousMap.compStarAlgHom'_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] (𝕜 : Type u_4) [i
nst_3 : CommSemiring 𝕜] (A : Type u_5) [inst_4 : TopologicalSpace A]   [inst_5 :
 Semiring A] [inst_6 : IsTopologicalSemiring A] [inst_7 : Star A] [inst_8 : Cont
inuousStar A]   [inst_9 : Algebra 𝕜 A] (g : C(Y, Z)) (f : C(X, Y)),   Continuous
Map.compStarAlgHom' 𝕜 A (g.comp f) =     (ContinuousMap.compStarAlgHom' 𝕜 A f).c
omp (ContinuousMap.compStarAlgHom' 𝕜 A g)
参数：𝕜 : Type u_4；A : Type u_5；g : C(Y, Z)；f : C(X, Y)；g.comp f；ContinuousMap.comp
StarAlgHom' 𝕜 A f；ContinuousMap.compStarAlgHom' 𝕜 A g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g

--- 原说明 ---
`ContinuousMap.compStarAlgHom'` is functorial.
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
/-
**ContinuousMap.compStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：compStarAlgHom (φ : A ->⋆ₐ[𝕜] B) (hφ : Continuous φ) : C(X, A) ->⋆ₐ[𝕜] C(X
, B) where toFun f
参数：φ : A ->⋆ₐ[𝕜] B；hφ : Continuous φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition with a continuous star algebra homomorphism is a star algebra h
omomorphism
between spaces of continuous maps.
-/
def compStarAlgHom (φ : A →⋆ₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) →⋆ₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_star φ (f x)

/-- `ContinuousMap.compStarAlgHom` sends the identity `StarAlgHom` on `A` to the identity
`StarAlgHom` on `C(X, A)`. -/
/-
**ContinuousMap.compStarAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, 
A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
`ContinuousMap.compStarAlgHom` sends the identity `StarAlgHom` on `A` to the ide
ntity
`StarAlgHom` on `C(X, A)`.
-/
lemma compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) := rfl

/-- `ContinuousMap.compStarAlgHom` is functorial. -/
/-
**ContinuousMap.compStarAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：compStarAlgHom_comp (φ : A ->⋆ₐ[𝕜] B) (ψ : B ->⋆ₐ[𝕜] C) (hφ : Continuous φ
) (hψ : Continuous ψ) : compStarAlgHom X (ψ.comp φ) (hψ.comp hφ) = (compStarAlgH
om X ψ hψ).comp (compStarAlgHom X φ hφ)
参数：φ : A ->⋆ₐ[𝕜] B；ψ : B ->⋆ₐ[𝕜] C；hφ : Continuous φ；hψ : Continuous ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)

--- 原说明 ---
`ContinuousMap.compStarAlgHom` is functorial.
-/
lemma compStarAlgHom_comp (φ : A →⋆ₐ[𝕜] B) (ψ : B →⋆ₐ[𝕜] C) (hφ : Continuous φ)
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
/-
**Homeomorph.compStarAlgEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A)
参数：f : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMap.compStarAlgHom'` as a `StarAlgEquiv` when the continuous map `f` 
is
actually a homeomorphism.
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
/-
**ContinuousMap.evalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.evalStarAlgHom [StarRing R] [ContinuousStar R] (x : X) : C(X
, R) ->⋆ₐ[S] R
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of continuous maps at a point, bundled as a star algebra homomorphism
.
-/
def ContinuousMap.evalStarAlgHom [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) →⋆ₐ[S] R :=
  { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }
