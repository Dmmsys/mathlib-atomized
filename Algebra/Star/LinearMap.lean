/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.WithConv
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Coalgebra.Convolution

/-! # Intrinsic star operation on linear maps

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

Because there is a global `star` instance on `H →ₗ[𝕜] H` (defined as the linear map adjoint on
finite-dimensional Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →ₗ[R] F)`.

The reason we chose `WithConv` is because together with the convolution product from
`Mathlib/RingTheory/Coalgebra/Convolution.lean`, we get a ⋆-algebra when
`star (WithConv.toConv comul) = WithConv.toConv (comm ∘ comul)`. -/

public section

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

open WithConv

namespace LinearMap

/--
Instance `intrinsicStar` / 实例 `intrinsicStar`

English:
instance intrinsicStar
  signature: : Star (WithConv (E ->ₗ[R] F)) where
  body: toConv
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }

中文:
实例 intrinsicStar
  签名: : Star (WithConv (E ->ₗ[R] F)) where
  定义体: toConv
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }

Depends on / 依赖: toConv
-/
instance intrinsicStar : Star (WithConv (E ->ₗ[R] F)) where
star f := toConv
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }

/--
theorem `intrinsicStar_apply` / 定理 `intrinsicStar_apply`

English:
theorem intrinsicStar_apply
  given: (f : WithConv (E ->ₗ[R] F)) (x : E)
  proof: rfl

中文:
定理 intrinsicStar_apply
  条件: (f : WithConv (E ->ₗ[R] F)) (x : E)
  证明: rfl
-/
@[simp] theorem intrinsicStar_apply (f : WithConv (E ->ₗ[R] F)) (x : E) :
    (star f) x = star (f (star x)) := rfl

/--
Instance `intrinsicInvolutiveStar` / 实例 `intrinsicInvolutiveStar`

English:
instance intrinsicInvolutiveStar
  signature: : InvolutiveStar (WithConv (E ->ₗ[R] F)) where
  body: by ext; simp

中文:
实例 intrinsicInvolutiveStar
  签名: : InvolutiveStar (WithConv (E ->ₗ[R] F)) where
  定义体: by ext; simp
-/
instance intrinsicInvolutiveStar : InvolutiveStar (WithConv (E ->ₗ[R] F)) where
  star_involutive x := by ext; simp

/--
Instance `intrinsicStarAddMonoid` / 实例 `intrinsicStarAddMonoid`

English:
instance intrinsicStarAddMonoid
  signature: : StarAddMonoid (WithConv (E ->ₗ[R] F)) where
  body: by ext; simp

中文:
实例 intrinsicStarAddMonoid
  签名: : StarAddMonoid (WithConv (E ->ₗ[R] F)) where
  定义体: by ext; simp
-/
instance intrinsicStarAddMonoid : StarAddMonoid (WithConv (E ->ₗ[R] F)) where
  star_add x y := by ext; simp

/--
theorem `IntrinsicStar.isSelfAdjoint_iff_map_star` / 定理 `IntrinsicStar.isSelfAdjoint_iff_map_star`

English:
theorem IntrinsicStar.isSelfAdjoint_iff_map_star
  given: (f : WithConv (E ->ₗ[R] F))
  proof: by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
    star_eq_iff_star_eq, eq_comm]

中文:
定理 IntrinsicStar.isSelfAdjoint_iff_map_star
  条件: (f : WithConv (E ->ₗ[R] F))
  证明: by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
    star_eq_iff_star_eq, eq_comm]

Depends on / 依赖: IsSelfAdjoint, LinearMap, LinearMap.ext_iff, WithConv, WithConv.ext_iff, eq_comm, ext_iff, intrinsicStar_apply, simp_rw, star_eq_iff_star_eq
-/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E ->ₗ[R] F)) :
    IsSelfAdjoint f ↔ forall x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
    star_eq_iff_star_eq, eq_comm]

/-- A star-preserving linear map is self-adjoint (with respect to the intrinsic star). -/
@[simp]
/--
theorem `_root_.IntrinsicStar.StarHomClass.isSelfAdjoint` / 定理 `_root_.IntrinsicStar.StarHomClass.isSelfAdjoint`

English:
theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint
  statement: {S : Type*} [FunLike S E F]
  proof: .mpr (map_star f) IntrinsicStar.isSelfAdjoint_iff_map_star _

中文:
定理 _root_.IntrinsicStar.StarHomClass.isSelfAdjoint
  结论: {S : 类型} [FunLike S E F]
  证明: .mpr (map_star f) IntrinsicStar.isSelfAdjoint_iff_map_star _
-/
protected theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} :
    IsSelfAdjoint (toConv (f : E ->ₗ[R] F) : WithConv (E ->ₗ[R] F)) :=
.mpr (map_star f) IntrinsicStar.isSelfAdjoint_iff_map_star _

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

/--
theorem `intrinsicStar_comp` / 定理 `intrinsicStar_comp`

English:
theorem intrinsicStar_comp
  given: (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] E))
  proof: by
  ext; simp

中文:
定理 intrinsicStar_comp
  条件: (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] E))
  证明: by
  ext; simp
-/
theorem intrinsicStar_comp (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] E)) :
    star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv ((star f).ofConv ∘ₗ (star g).ofConv) := by
  ext; simp

/--
theorem `intrinsicStar_comp'` / 定理 `intrinsicStar_comp'`

English:
theorem intrinsicStar_comp'
  given: (f : E ->ₗ[R] F) (g : G ->ₗ[R] E)
  proof: by
  simpa using intrinsicStar_comp _ _

中文:
定理 intrinsicStar_comp'
  条件: (f : E ->ₗ[R] F) (g : G ->ₗ[R] E)
  证明: by
  simpa using intrinsicStar_comp _ _

Depends on / 依赖: intrinsicStar_comp
-/
theorem intrinsicStar_comp' (f : E ->ₗ[R] F) (g : G ->ₗ[R] E) :
    star (toConv (f ∘ₗ g)) = toConv ((star (toConv f)).ofConv ∘ₗ (star (toConv g)).ofConv) := by
  simpa using intrinsicStar_comp _ _

/--
theorem `intrinsicStar_id` / 定理 `intrinsicStar_id`

English:
theorem intrinsicStar_id
  proof: by ext; simp

中文:
定理 intrinsicStar_id
  证明: by ext; simp
-/
@[simp] theorem intrinsicStar_id :
    star (toConv (LinearMap.id (R := R) (M := E))) = toConv LinearMap.id := by ext; simp
/--
theorem `intrinsicStar_zero` / 定理 `intrinsicStar_zero`

English:
theorem intrinsicStar_zero
  statement: star (0 : WithConv (E ->ₗ[R] F)) = 0
  proof: by simp

中文:
定理 intrinsicStar_zero
  结论: star (0 : WithConv (E ->ₗ[R] F)) = 0
  证明: by simp
-/
theorem intrinsicStar_zero : star (0 : WithConv (E ->ₗ[R] F)) = 0 := by simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

/--
theorem `intrinsicStar_mulLeft` / 定理 `intrinsicStar_mulLeft`

English:
theorem intrinsicStar_mulLeft
  given: (x : E)
  proof: by ext; simp

中文:
定理 intrinsicStar_mulLeft
  条件: (x : E)
  证明: by ext; simp
-/
theorem intrinsicStar_mulLeft (x : E) :
    star (toConv (mulLeft R x)) = toConv (mulRight R (star x)) := by ext; simp

/--
theorem `intrinsicStar_mulRight` / 定理 `intrinsicStar_mulRight`

English:
theorem intrinsicStar_mulRight
  given: (x : E)
  proof: by
  rw [star_eq_iff_star_eq]; rw [intrinsicStar_mulLeft]; rw [star_star]

中文:
定理 intrinsicStar_mulRight
  条件: (x : E)
  证明: by
  rw [star_eq_iff_star_eq]; rw [intrinsicStar_mulLeft]; rw [star_star]

Depends on / 依赖: intrinsicStar_mulLeft, star_eq_iff_star_eq, star_star
-/
theorem intrinsicStar_mulRight (x : E) :
    star (toConv (mulRight R x)) = toConv (mulLeft R (star x)) := by
  rw [star_eq_iff_star_eq]; rw [intrinsicStar_mulLeft]; rw [star_star]

/--
theorem `intrinsicStar_mul'` / 定理 `intrinsicStar_mul'`

English:
theorem intrinsicStar_mul'
  given: [SMulCommClass R' E E] [IsScalarTower R' E E]
  proof: WithConv.ext TensorProduct.ext' fun _ _ => by simp

中文:
定理 intrinsicStar_mul'
  条件: [SMulCommClass R' E E] [IsScalarTower R' E E]
  证明: WithConv.ext TensorProduct.ext' fun _ _ => by simp

Depends on / 依赖: TensorProduct, TensorProduct.ext, WithConv, WithConv.ext
-/
theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (toConv (mul' R' E)) = toConv (mul' R' E ∘ₗ TensorProduct.comm R' E E) :=
WithConv.ext TensorProduct.ext' fun _ _ => by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
/--
Instance `intrinsicStarModule` / 实例 `intrinsicStarModule`

English:
instance intrinsicStarModule
  signature: : StarModule R (WithConv (E ->ₗ[R] F)) where
  body: by ext; simp

中文:
实例 intrinsicStarModule
  签名: : StarModule R (WithConv (E ->ₗ[R] F)) where
  定义体: by ext; simp
-/
instance intrinsicStarModule : StarModule R (WithConv (E ->ₗ[R] F)) where
  star_smul _ _ := by ext; simp

section CommSemiring
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

/--
theorem `_root_.TensorProduct.intrinsicStar_map` / 定理 `_root_.TensorProduct.intrinsicStar_map`

English:
theorem _root_.TensorProduct.intrinsicStar_map
  proof: WithConv.ext TensorProduct.ext' fun _ _ => by simp

中文:
定理 _root_.TensorProduct.intrinsicStar_map
  证明: WithConv.ext TensorProduct.ext' fun _ _ => by simp

Depends on / 依赖: TensorProduct, TensorProduct.ext, WithConv, WithConv.ext
-/
theorem _root_.TensorProduct.intrinsicStar_map
    (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] H)) :
    star (toConv (TensorProduct.map f.ofConv g.ofConv)) =
      toConv (TensorProduct.map (star f).ofConv (star g).ofConv) :=
WithConv.ext TensorProduct.ext' fun _ _ => by simp

/--
theorem `_root_.TensorProduct.star_map_apply_eq_map_intrinsicStar` / 定理 `_root_.TensorProduct.star_map_apply_eq_map_intrinsicStar`

English:
theorem _root_.TensorProduct.star_map_apply_eq_map_intrinsicStar
  proof: by
  simpa using congr($(TensorProduct.intrinsicStar_map f g) (star x))

中文:
定理 _root_.TensorProduct.star_map_apply_eq_map_intrinsicStar
  证明: by
  simpa using congr($(TensorProduct.intrinsicStar_map f g) (star x))

Depends on / 依赖: TensorProduct, TensorProduct.intrinsicStar_map, intrinsicStar_map
-/
theorem _root_.TensorProduct.star_map_apply_eq_map_intrinsicStar
    (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] H)) (x) :
    star (TensorProduct.map f.ofConv g.ofConv x) =
      TensorProduct.map (star f).ofConv (star g).ofConv (star x) := by
  simpa using congr($(TensorProduct.intrinsicStar_map f g) (star x))

/--
theorem `intrinsicStar_lTensor` / 定理 `intrinsicStar_lTensor`

English:
theorem intrinsicStar_lTensor
  given: (f : WithConv (F ->ₗ[R] G))
  proof: by ext; simp

中文:
定理 intrinsicStar_lTensor
  条件: (f : WithConv (F ->ₗ[R] G))
  证明: by ext; simp
-/
theorem intrinsicStar_lTensor (f : WithConv (F ->ₗ[R] G)) :
    star (toConv (lTensor E f.ofConv)) = toConv (lTensor E (star f).ofConv) := by ext; simp

/--
theorem `intrinsicStar_rTensor` / 定理 `intrinsicStar_rTensor`

English:
theorem intrinsicStar_rTensor
  given: (f : WithConv (E ->ₗ[R] F))
  proof: by ext; simp

中文:
定理 intrinsicStar_rTensor
  条件: (f : WithConv (E ->ₗ[R] F))
  证明: by ext; simp
-/
theorem intrinsicStar_rTensor (f : WithConv (E ->ₗ[R] F)) :
    star (toConv (rTensor G f.ofConv)) = toConv (rTensor G (star f).ofConv) := by ext; simp

/--
theorem `intrinsicStar_eq_comp` / 定理 `intrinsicStar_eq_comp`

English:
theorem intrinsicStar_eq_comp
  given: (f : WithConv (E ->ₗ[R] F))
  proof: rfl

中文:
定理 intrinsicStar_eq_comp
  条件: (f : WithConv (E ->ₗ[R] F))
  证明: rfl
-/
theorem intrinsicStar_eq_comp (f : WithConv (E ->ₗ[R] F)) :
    star f =
      toConv ((starLinearEquiv R).toLinearMap ∘ₛₗ f.ofConv ∘ₛₗ (starLinearEquiv R).toLinearMap) :=
  rfl

/--
theorem `IntrinsicStar.starLinearEquiv_eq_arrowCongr` / 定理 `IntrinsicStar.starLinearEquiv_eq_arrowCongr`

English:
theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr
  proof: rfl

中文:
定理 IntrinsicStar.starLinearEquiv_eq_arrowCongr
  证明: rfl

Depends on / 依赖: WithConv
-/
theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := WithConv (E ->ₗ[R] F)) =
      (WithConv.linearEquiv R _).trans
      (((starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans
        (WithConv.linearEquiv R _).symm) := rfl

end CommSemiring

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

/--
theorem `intrinsicStar_toSpanSingleton` / 定理 `intrinsicStar_toSpanSingleton`

English:
theorem intrinsicStar_toSpanSingleton
  given: (a : E)
  proof: by ext; simp

中文:
定理 intrinsicStar_toSpanSingleton
  条件: (a : E)
  证明: by ext; simp
-/
@[simp] theorem intrinsicStar_toSpanSingleton (a : E) :
    star (toConv (toSpanSingleton S E a)) = toConv (toSpanSingleton S E (star a)) := by ext; simp

/--
theorem `intrinsicStar_smulRight` / 定理 `intrinsicStar_smulRight`

English:
theorem intrinsicStar_smulRight
  given: [Module S F] [StarModule S F] (f : WithConv (E ->ₗ[S] S)) (x : F)
  proof: by
  ext; simp

中文:
定理 intrinsicStar_smulRight
  条件: [Module S F] [StarModule S F] (f : WithConv (E ->ₗ[S] S)) (x : F)
  证明: by
  ext; simp
-/
theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : WithConv (E ->ₗ[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

section convRing
variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarRing A] [StarModule R A]
  [AddCommMonoid C] [Module R C] [StarAddMonoid C] [StarModule R C]

open Coalgebra TensorProduct

/--
theorem `intrinsicStar_convMul` / 定理 `intrinsicStar_convMul`

English:
theorem intrinsicStar_convMul
  statement: [CoalgebraStruct R C]
  proof: by
  simp_rw [convMul_def, intrinsicStar_comp', intrinsicStar_mul', intrinsicStar_map,
    h, comp_assoc, ← comp_assoc _ _ (map _ _), map_comp_comm_eq,
    ← comp_assoc _ (TensorProduct.comm R A A).toLinearMap]
  ext; simp

中文:
定理 intrinsicStar_convMul
  结论: [CoalgebraStruct R C]
  证明: by
  simp_rw [convMul_def, intrinsicStar_comp', intrinsicStar_mul', intrinsicStar_map,
    h, comp_assoc, ← comp_assoc _ _ (map _ _), map_comp_comm_eq,
    ← comp_assoc _ (TensorProduct.comm R A A).toLinearMap]
  ext; simp

Depends on / 依赖: TensorProduct, TensorProduct.comm, comp_assoc, convMul_def, intrinsicStar_comp, intrinsicStar_map, intrinsicStar_mul, map_comp_comm_eq, simp_rw, toLinearMap
-/
theorem intrinsicStar_convMul [CoalgebraStruct R C]
    (h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul))
    (f g : WithConv (C ->ₗ[R] A)) : star (f * g) = star g * star f := by
  simp_rw [convMul_def, intrinsicStar_comp', intrinsicStar_mul', intrinsicStar_map,
    h, comp_assoc, ← comp_assoc _ _ (map _ _), map_comp_comm_eq,
    ← comp_assoc _ (TensorProduct.comm R A A).toLinearMap]
  ext; simp

/--
Definition of `convIntrinsicStarRing` / `convIntrinsicStarRing` 的定义

English:
abbreviation convIntrinsicStarRing
  signature: [Coalgebra R C]
  body: intrinsicStarAddMonoid
  star_mul := intrinsicStar_convMul h

中文:
缩写 convIntrinsicStarRing
  签名: [Coalgebra R C]
  定义体: intrinsicStarAddMonoid
  star_mul := intrinsicStar_convMul h

Depends on / 依赖: intrinsicStarAddMonoid
-/
abbrev convIntrinsicStarRing [Coalgebra R C]
    (h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul)) :
    StarRing (WithConv (C ->ₗ[R] A)) where
  __ := intrinsicStarAddMonoid
  star_mul := intrinsicStar_convMul h

variable {n : Type*} [DecidableEq n] {B : n -> Type*} [Π i, AddCommMonoid (B i)]
  [Π i, Module R (B i)] [Π i, StarAddMonoid (B i)] [forall i, StarModule R (B i)]

/--
theorem `intrinsicStar_single` / 定理 `intrinsicStar_single`

English:
theorem intrinsicStar_single
  given: (i : n)
  proof: by
  aesop (add simp [Pi.single, Function.update])

中文:
定理 intrinsicStar_single
  条件: (i : n)
  证明: by
  aesop (add simp [Pi.single, Function.update])
-/
@[simp] theorem intrinsicStar_single (i : n) :
    star (toConv (single R B i)) = toConv (single R B i) := by
  aesop (add simp [Pi.single, Function.update])

variable [Fintype n]

/--
theorem `_root_.Pi.intrinsicStar_comul` / 定理 `_root_.Pi.intrinsicStar_comul`

English:
theorem _root_.Pi.intrinsicStar_comul
  statement: [Π i, CoalgebraStruct R (B i)]
  proof: by
  ext i x
  have := by simpa using congr($(h i) x)
  simp only [coe_comp, coe_single, Function.comp_apply, intrinsicStar_apply, Pi.star_single,
    Pi.comul_single, LinearEquiv.coe_coe]
  rw [star_map_apply_eq_map_intrinsicStar]; rw [this]; rw [map_comm]
  simp

中文:
定理 _root_.Pi.intrinsicStar_comul
  结论: [Π i, CoalgebraStruct R (B i)]
  证明: by
  ext i x
  have := by simpa using congr($(h i) x)
  simp only [coe_comp, coe_single, Function.comp_apply, intrinsicStar_apply, Pi.star_single,
    Pi.comul_single, LinearEquiv.coe_coe]
  rw [star_map_apply_eq_map_intrinsicStar]; rw [this]; rw [map_comm]
  simp
-/
theorem _root_.Pi.intrinsicStar_comul [Π i, CoalgebraStruct R (B i)]
    (h : forall i, star (toConv (comul (R := R) (A := B i))) =
      toConv (TensorProduct.comm R (B i) (B i) ∘ₗ comul)) :
    star (toConv (comul (R := R) (A := Π i, B i))) =
      toConv (TensorProduct.comm R (Π i, B i) (Π i, B i) ∘ₗ comul) := by
  ext i x
  have := by simpa using congr($(h i) x)
  simp only [coe_comp, coe_single, Function.comp_apply, intrinsicStar_apply, Pi.star_single,
    Pi.comul_single, LinearEquiv.coe_coe]
  rw [star_map_apply_eq_map_intrinsicStar]; rw [this]; rw [map_comm]
  simp

/--
theorem `_root_.Pi.intrinsicStar_comul_commSemiring` / 定理 `_root_.Pi.intrinsicStar_comul_commSemiring`

English:
theorem _root_.Pi.intrinsicStar_comul_commSemiring
  proof: Pi.intrinsicStar_comul fun _ => by ext; simp

中文:
定理 _root_.Pi.intrinsicStar_comul_commSemiring
  证明: Pi.intrinsicStar_comul fun _ => by ext; simp
-/
@[simp] theorem _root_.Pi.intrinsicStar_comul_commSemiring :
    star (toConv (comul (R := R) (A := n -> R))) =
      toConv (TensorProduct.comm R (n -> R) (n -> R) ∘ₗ comul) :=
  Pi.intrinsicStar_comul fun _ => by ext; simp

/--
Instance `_root_.Pi.convIntrinsicStarRingCommSemiring` / 实例 `_root_.Pi.convIntrinsicStarRingCommSemiring`

English:
instance _root_.Pi.convIntrinsicStarRingCommSemiring
  signature: {m : Type*}
  body: convIntrinsicStarRing (by simp)

中文:
实例 _root_.Pi.convIntrinsicStarRingCommSemiring
  签名: {m : 类型}
  定义体: convIntrinsicStarRing (by simp)

Depends on / 依赖: convIntrinsicStarRing
-/
instance _root_.Pi.convIntrinsicStarRingCommSemiring {m : Type*} :
    StarRing (WithConv ((n -> R) ->ₗ[R] m -> R)) := convIntrinsicStarRing (by simp)

end convRing

end LinearMap

section matrix
variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

namespace LinearMap

/--
theorem `toMatrix'_intrinsicStar` / 定理 `toMatrix'_intrinsicStar`

English:
theorem toMatrix'_intrinsicStar
  given: (f : WithConv ((m -> R) ->ₗ[R] (n -> R)))
  proof: by
  ext; simp

中文:
定理 toMatrix'_intrinsicStar
  条件: (f : WithConv ((m -> R) ->ₗ[R] (n -> R)))
  证明: by
  ext; simp
-/
theorem toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ[R] (n -> R))) :
    (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star := by
  ext; simp

/--
theorem `IntrinsicStar.isSelfAdjoint_iff_toMatrix'` / 定理 `IntrinsicStar.isSelfAdjoint_iff_toMatrix'`

English:
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix'
  given: (f : WithConv ((m -> R) ->ₗ[R] (n -> R)))
  proof: by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

中文:
定理 IntrinsicStar.isSelfAdjoint_iff_toMatrix'
  条件: (f : WithConv ((m -> R) ->ₗ[R] (n -> R)))
  证明: by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

Depends on / 依赖: IsSelfAdjoint, Matrix, Matrix.ext_iff, WithConv, WithConv.ext_iff, _intrinsicStar, eq_iff, ext_iff, injective, injective.eq_iff, toMatrix
-/
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : WithConv ((m -> R) ->ₗ[R] (n -> R))) :
    IsSelfAdjoint f ↔ forall i j, IsSelfAdjoint (f.ofConv.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

end LinearMap

namespace Matrix

/--
theorem `intrinsicStar_toLin'` / 定理 `intrinsicStar_toLin'`

English:
theorem intrinsicStar_toLin'
  given: (A : Matrix n m R)
  proof: by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

中文:
定理 intrinsicStar_toLin'
  条件: (A : Matrix n m R)
  证明: by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, WithConv, WithConv.ext_iff, _intrinsicStar, eq_iff, ext_iff, injective, injective.eq_iff, toMatrix
-/
theorem intrinsicStar_toLin' (A : Matrix n m R) :
    star (toConv A.toLin') = toConv (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

/--
theorem `IntrinsicStar.isSelfAdjoint_toLin'_iff` / 定理 `IntrinsicStar.isSelfAdjoint_toLin'_iff`

English:
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff
  given: (A : Matrix n m R)
  proof: by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

中文:
定理 IntrinsicStar.isSelfAdjoint_toLin'_iff
  条件: (A : Matrix n m R)
  证明: by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

Depends on / 依赖: Equation, IsSelfAdjoint, eval_map, ext_iff, intrinsicStar_toLin, map_polynomial, map_zero
-/
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint (toConv A.toLin') ↔ forall i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

end Matrix
end matrix

namespace Module.End

/--
Instance `Units.intrinsicStar` / 实例 `Units.intrinsicStar`

English:
instance Units.intrinsicStar
  signature: : Star (WithConv (End R E)ˣ) where
  body: toConv by
    refine ⟨(star (toConv ↑f.ofConv : WithConv (End R E))).ofConv,
      (star (toConv ↑(f.ofConv⁻¹ : (End R E)ˣ))).ofConv, ?_, ?_⟩
    all_goals
      rw [mul_eq_comp]; rw [← toConv_injective.eq_iff]; rw [← LinearMap.intrinsicStar_comp']
      simp [← mul_eq_comp, one_eq_id]

中文:
实例 Units.intrinsicStar
  签名: : Star (WithConv (End R E)ˣ) where
  定义体: toConv by
    refine ⟨(star (toConv ↑f.ofConv : WithConv (End R E))).ofConv,
      (star (toConv ↑(f.ofConv⁻¹ : (End R E)ˣ))).ofConv, ?_, ?_⟩
    all_goals
      rw [mul_eq_comp]; rw [← toConv_injective.eq_iff]; rw [← LinearMap.intrinsicStar_comp']
      simp [← mul_eq_comp, one_eq_id]

Depends on / 依赖: LinearMap, LinearMap.intrinsicStar_comp, WithConv, all_goals, eq_iff, f.ofConv, intrinsicStar_comp, mul_eq_comp, ofConv, one_eq_id, toConv, toConv_injective, toConv_injective.eq_iff
-/
instance Units.intrinsicStar : Star (WithConv (End R E)ˣ) where
star f := toConv by
    refine ⟨(star (toConv ↑f.ofConv : WithConv (End R E))).ofConv,
      (star (toConv ↑(f.ofConv⁻¹ : (End R E)ˣ))).ofConv, ?_, ?_⟩
    all_goals
      rw [mul_eq_comp]; rw [← toConv_injective.eq_iff]; rw [← LinearMap.intrinsicStar_comp']
      simp [← mul_eq_comp, one_eq_id]

/--
theorem `IsUnit.intrinsicStar` / 定理 `IsUnit.intrinsicStar`

English:
theorem IsUnit.intrinsicStar
  given: {f : WithConv (End R E)} (hf : IsUnit f.ofConv)
  proof: by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

中文:
定理 IsUnit.intrinsicStar
  条件: {f : WithConv (End R E)} (hf : IsUnit f.ofConv)
  证明: by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

Depends on / 依赖: IsUnit, isUnit, ofConv, ofConv.isUnit, toConv
-/
theorem IsUnit.intrinsicStar {f : WithConv (End R E)} (hf : IsUnit f.ofConv) :
    IsUnit (star f).ofConv := by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

open Module.End in
/--
theorem `isUnit_intrinsicStar_iff` / 定理 `isUnit_intrinsicStar_iff`

English:
theorem isUnit_intrinsicStar_iff
  given: {f : WithConv (End R E)}
  proof: ⟨fun h => star_star f ▸ h.intrinsicStar, fun h => h.intrinsicStar⟩

中文:
定理 isUnit_intrinsicStar_iff
  条件: {f : WithConv (End R E)}
  证明: ⟨fun h => star_star f ▸ h.intrinsicStar, fun h => h.intrinsicStar⟩
-/
@[simp] theorem isUnit_intrinsicStar_iff {f : WithConv (End R E)} :
    IsUnit (star f).ofConv ↔ IsUnit f.ofConv :=
  ⟨fun h => star_star f ▸ h.intrinsicStar, fun h => h.intrinsicStar⟩

section eigenspace
variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

open LinearMap

/--
theorem `mem_eigenspace_intrinsicStar_iff` / 定理 `mem_eigenspace_intrinsicStar_iff`

English:
theorem mem_eigenspace_intrinsicStar_iff
  given: (f : WithConv (End R V)) (α : R) (x : V)
  proof: by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]

中文:
定理 mem_eigenspace_intrinsicStar_iff
  条件: (f : WithConv (End R V)) (α : R) (x : V)
  证明: by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, intrinsicStar_apply, mem_eigenspace_iff, simp_rw, star_eq_iff_star_eq, star_smul
-/
theorem mem_eigenspace_intrinsicStar_iff (f : WithConv (End R V)) (α : R) (x : V) :
    x in (star f).ofConv.eigenspace α ↔ star x in f.ofConv.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]
/--
theorem `spectrum_intrinsicStar` / 定理 `spectrum_intrinsicStar`

English:
theorem spectrum_intrinsicStar
  given: (f : WithConv (End R V))
  proof: by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

中文:
定理 spectrum_intrinsicStar
  条件: (f : WithConv (End R V))
  证明: by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Set.mem_star, algebraMap_eq_smul_one, isUnit_intrinsicStar_iff, mem_iff, mem_star, not_iff_not, one_eq_id, simp_rw, spectrum, spectrum.mem_iff
-/
theorem spectrum_intrinsicStar (f : WithConv (End R V)) :
    spectrum R (star f).ofConv = star (spectrum R f.ofConv) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

end eigenspace
end Module.End
