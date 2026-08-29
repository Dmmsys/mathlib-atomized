/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Ring

/-!
# Internally-graded rings and algebras

This file defines the typeclass `GradedAlgebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → Submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `GradedRing 𝒜`: the typeclass, which is a combination of `SetLike.GradedMonoid`, and
  `DirectSum.Decomposition 𝒜`.
* `GradedAlgebra 𝒜`: A convenience alias for `GradedRing` when `𝒜` is a family of submodules.
* `DirectSum.decomposeRingEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `DirectSum.decomposeAlgEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `GradedAlgebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → Submodule ℕ A` and `𝒜 : ι → Submodule ℤ A` respectively, since all
`Semiring`s are ℕ-algebras via `Semiring.toNatAlgebra`, and all `Ring`s are `ℤ`-algebras via
`Ring.toIntAlgebra`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

@[expose] public section


open DirectSum

variable {ι R A σ : Type*}

section GradedRing

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ)

open DirectSum

/--
Definition of `GradedRing` / `GradedRing` 的定义

English:
class GradedRing
  parameters: (𝒜 : ι -> σ)
  extends: SetLike.GradedMonoid 𝒜, DirectSum.Decomposition 𝒜
  (no additional axioms)

中文:
类 分次环
  参数: (𝒜 : ι -> σ)
  继承: 集合状.分次幺半群 𝒜, 直和.分解 𝒜
  (无附加公理)
-/
class GradedRing (𝒜 : ι -> σ) extends SetLike.GradedMonoid 𝒜, DirectSum.Decomposition 𝒜

variable [GradedRing 𝒜]

namespace DirectSum

/--
Definition of `decomposeRingEquiv` / `decomposeRingEquiv` 的定义

English:
definition decomposeRingEquiv
  signature: : A ≃+* ⨁ i, 𝒜 i
  body: RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }

@[simp]

中文:
定义 decomposeRingEquiv
  签名: : A ≃+* ⨁ i, 𝒜 i
  定义体: RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.symm, coeRingHom, decomposeAddEquiv, map_mul
-/
def decomposeRingEquiv : A ≃+* ⨁ i, 𝒜 i :=
  RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }

@[simp]
/--
theorem `decompose_one` / 定理 `decompose_one`

English:
theorem decompose_one
  statement: decompose 𝒜 (1 : A) = 1
  proof: map_one (decomposeRingEquiv 𝒜)

@[simp]

中文:
定理 decompose_one
  结论: decompose 𝒜 (1 : A) = 1
  证明: map_one (decomposeRingEquiv 𝒜)

@[simp]

Depends on / 依赖: decomposeRingEquiv, map_one
-/
theorem decompose_one : decompose 𝒜 (1 : A) = 1 :=
  map_one (decomposeRingEquiv 𝒜)

@[simp]
/--
theorem `decompose_symm_one` / 定理 `decompose_symm_one`

English:
theorem decompose_symm_one
  statement: (decompose 𝒜).symm 1 = (1 : A)
  proof: map_one (decomposeRingEquiv 𝒜).symm

@[simp]

中文:
定理 decompose_symm_one
  结论: (decompose 𝒜).symm 1 = (1 : A)
  证明: map_one (decomposeRingEquiv 𝒜).symm

@[simp]

Depends on / 依赖: decomposeRingEquiv, map_one
-/
theorem decompose_symm_one : (decompose 𝒜).symm 1 = (1 : A) :=
  map_one (decomposeRingEquiv 𝒜).symm

@[simp]
/--
theorem `decompose_mul` / 定理 `decompose_mul`

English:
theorem decompose_mul
  given: (x y : A)
  statement: decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y
  proof: map_mul (decomposeRingEquiv 𝒜) x y

@[simp]

中文:
定理 decompose_mul
  条件: (x y : A)
  结论: decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y
  证明: map_mul (decomposeRingEquiv 𝒜) x y

@[simp]

Depends on / 依赖: decomposeRingEquiv, map_mul
-/
theorem decompose_mul (x y : A) : decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y :=
  map_mul (decomposeRingEquiv 𝒜) x y

@[simp]
/--
theorem `decompose_symm_mul` / 定理 `decompose_symm_mul`

English:
theorem decompose_symm_mul
  given: (x y : ⨁ i, 𝒜 i)
  proof: map_mul (decomposeRingEquiv 𝒜).symm x y

中文:
定理 decompose_symm_mul
  条件: (x y : ⨁ i, 𝒜 i)
  证明: map_mul (decomposeRingEquiv 𝒜).symm x y

Depends on / 依赖: decomposeRingEquiv, map_mul
-/
theorem decompose_symm_mul (x y : ⨁ i, 𝒜 i) :
    (decompose 𝒜).symm (x * y) = (decompose 𝒜).symm x * (decompose 𝒜).symm y :=
  map_mul (decomposeRingEquiv 𝒜).symm x y

end DirectSum

/--
Definition of `GradedRing.proj` / `GradedRing.proj` 的定义

English:
definition GradedRing.proj
  signature: (i : ι)
  body: (AddSubmonoidClass.subtype (𝒜 i)).comp
(DFinsupp.evalAddMonoidHom i).comp
RingHom.toAddMonoidHom RingEquiv.toRingHom DirectSum.decomposeRingEquiv 𝒜

@[simp]

中文:
定义 分次环.proj
  签名: (i : ι)
  定义体: (AddSubmonoidClass.subtype (𝒜 i)).comp
(DFinsupp.evalAddMonoidHom i).comp
RingHom.toAddMonoidHom RingEquiv.toRingHom DirectSum.decomposeRingEquiv 𝒜

@[simp]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.subtype, DFinsupp, DFinsupp.evalAddMonoidHom, DirectSum, DirectSum.decomposeRingEquiv, RingEquiv, RingEquiv.toRingHom, RingHom, RingHom.toAddMonoidHom, decomposeRingEquiv, evalAddMonoidHom, subtype, toAddMonoidHom, toRingHom
-/
def GradedRing.proj (i : ι) : A ->+ A :=
(AddSubmonoidClass.subtype (𝒜 i)).comp
(DFinsupp.evalAddMonoidHom i).comp
RingHom.toAddMonoidHom RingEquiv.toRingHom DirectSum.decomposeRingEquiv 𝒜

@[simp]
/--
theorem `GradedRing.proj_apply` / 定理 `GradedRing.proj_apply`

English:
theorem GradedRing.proj_apply
  given: (i : ι) (r : A)
  proof: rfl

中文:
定理 分次环.proj_apply
  条件: (i : ι) (r : A)
  证明: rfl
-/
theorem GradedRing.proj_apply (i : ι) (r : A) :
    GradedRing.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl

/--
theorem `GradedRing.proj_recompose` / 定理 `GradedRing.proj_recompose`

English:
theorem GradedRing.proj_recompose
  given: (a : ⨁ i, 𝒜 i) (i : ι)
  proof: by
  rw [GradedRing.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

中文:
定理 分次环.proj_recompose
  条件: (a : ⨁ i, 𝒜 i) (i : ι)
  证明: by
  rw [GradedRing.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, GradedRing, GradedRing.proj_apply, apply_symm_apply, decompose_symm_of, proj_apply
-/
theorem GradedRing.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedRing.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (DirectSum.of _ i (a i)) := by
  rw [GradedRing.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

/--
theorem `GradedRing.mem_support_iff` / 定理 `GradedRing.mem_support_iff`

English:
theorem GradedRing.mem_support_iff
  given: [forall (i) (x : 𝒜 i), Decidable (x != 0)] (r : A) (i : ι)
  proof: DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm

中文:
定理 分次环.mem_support_iff
  条件: [对任意 (i) (x : 𝒜 i), 可判定 (x != 0)] (r : A) (i : ι)
  证明: DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_iff.trans, ZeroMemClass, ZeroMemClass.coe_eq_zero.not.symm, coe_eq_zero, mem_support_iff
-/
theorem GradedRing.mem_support_iff [forall (i) (x : 𝒜 i), Decidable (x != 0)] (r : A) (i : ι) :
    i in (decompose 𝒜 r).support ↔ GradedRing.proj 𝒜 i r != 0 :=
  DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm

end GradedRing

section AddCancelMonoid

open DirectSum

variable [DecidableEq ι] [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ)
variable {i j : ι}

namespace DirectSum

/--
theorem `coe_decompose_mul_add_of_left_mem` / 定理 `coe_decompose_mul_add_of_left_mem`

English:
theorem coe_decompose_mul_add_of_left_mem
  statement: [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b : A}
  proof: by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_add]

中文:
定理 coe_decompose_mul_add_of_left_mem
  结论: [加法左消去幺半群 ι] [分次环 𝒜] {a b : A}
  证明: by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_add]

Depends on / 依赖: a_mem, coe_of_mul_apply_add, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_add_of_left_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a in 𝒜 i) : (decompose 𝒜 (a * b) (i + j) : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_add]

/--
theorem `coe_decompose_mul_add_of_right_mem` / 定理 `coe_decompose_mul_add_of_right_mem`

English:
theorem coe_decompose_mul_add_of_right_mem
  statement: [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b : A}
  proof: by
  lift b to 𝒜 j using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_add]

中文:
定理 coe_decompose_mul_add_of_right_mem
  结论: [加法右消去幺半群 ι] [分次环 𝒜] {a b : A}
  证明: by
  lift b to 𝒜 j using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_add]

Depends on / 依赖: b_mem, coe_mul_of_apply_add, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_add_of_right_mem [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b in 𝒜 j) : (decompose 𝒜 (a * b) (i + j) : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 j using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_add]

/--
theorem `decompose_mul_add_left` / 定理 `decompose_mul_add_left`

English:
theorem decompose_mul_add_left
  given: [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a : 𝒜 i) {b : A}
  proof: Subtype.ext coe_decompose_mul_add_of_left_mem 𝒜 a.2

中文:
定理 decompose_mul_add_left
  条件: [加法左消去幺半群 ι] [分次环 𝒜] (a : 𝒜 i) {b : A}
  证明: Subtype.ext coe_decompose_mul_add_of_left_mem 𝒜 a.2

Depends on / 依赖: Subtype, Subtype.ext, coe_decompose_mul_add_of_left_mem
-/
theorem decompose_mul_add_left [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a : 𝒜 i) {b : A} :
    decompose 𝒜 (↑a * b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ a (decompose 𝒜 b j) :=
Subtype.ext coe_decompose_mul_add_of_left_mem 𝒜 a.2

/--
theorem `decompose_mul_add_right` / 定理 `decompose_mul_add_right`

English:
theorem decompose_mul_add_right
  given: [AddRightCancelMonoid ι] [GradedRing 𝒜] {a : A} (b : 𝒜 j)
  proof: Subtype.ext coe_decompose_mul_add_of_right_mem 𝒜 b.2

中文:
定理 decompose_mul_add_right
  条件: [加法右消去幺半群 ι] [分次环 𝒜] {a : A} (b : 𝒜 j)
  证明: Subtype.ext coe_decompose_mul_add_of_right_mem 𝒜 b.2

Depends on / 依赖: Subtype, Subtype.ext, coe_decompose_mul_add_of_right_mem
-/
theorem decompose_mul_add_right [AddRightCancelMonoid ι] [GradedRing 𝒜] {a : A} (b : 𝒜 j) :
    decompose 𝒜 (a * ↑b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ (decompose 𝒜 a i) b :=
Subtype.ext coe_decompose_mul_add_of_right_mem 𝒜 b.2

/--
theorem `coe_decompose_mul_of_left_mem_zero` / 定理 `coe_decompose_mul_of_left_mem_zero`

English:
theorem coe_decompose_mul_of_left_mem_zero
  statement: [AddMonoid ι] [GradedRing 𝒜] {a b : A}
  proof: by
  lift a to 𝒜 0 using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_of_mem_zero]

中文:
定理 coe_decompose_mul_of_left_mem_zero
  结论: [加法幺半群 ι] [分次环 𝒜] {a b : A}
  证明: by
  lift a to 𝒜 0 using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_of_mem_zero]

Depends on / 依赖: a_mem, coe_of_mul_apply_of_mem_zero, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_left_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a in 𝒜 0) : (decompose 𝒜 (a * b) j : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 0 using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply_of_mem_zero]

/--
theorem `coe_decompose_mul_of_right_mem_zero` / 定理 `coe_decompose_mul_of_right_mem_zero`

English:
theorem coe_decompose_mul_of_right_mem_zero
  statement: [AddMonoid ι] [GradedRing 𝒜] {a b : A}
  proof: by
  lift b to 𝒜 0 using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_of_mem_zero]

中文:
定理 coe_decompose_mul_of_right_mem_zero
  结论: [加法幺半群 ι] [分次环 𝒜] {a b : A}
  证明: by
  lift b to 𝒜 0 using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_of_mem_zero]

Depends on / 依赖: b_mem, coe_mul_of_apply_of_mem_zero, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_right_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b in 𝒜 0) : (decompose 𝒜 (a * b) i : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 0 using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply_of_mem_zero]

end DirectSum

end AddCancelMonoid

section GradedAlgebra

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝒜 : ι -> Submodule R A)

/--
Definition of `GradedAlgebra` / `GradedAlgebra` 的定义

English:
abbreviation GradedAlgebra
  body: GradedRing 𝒜

中文:
缩写 分次代数
  定义体: GradedRing 𝒜

Depends on / 依赖: GradedRing
-/
abbrev GradedAlgebra :=
  GradedRing 𝒜

/--
Definition of `GradedAlgebra.ofAlgHom` / `GradedAlgebra.ofAlgHom` 的定义

English:
abbreviation GradedAlgebra.ofAlgHom
  signature: [SetLike.GradedMonoid 𝒜] (decompose : A ->ₐ[R] ⨁ i, 𝒜 i)
  body: decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices decompose.comp (DirectSum.coeAlgHom 𝒜) = AlgHom.id _ _ from AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)

中文:
缩写 分次代数.ofAlgHom
  签名: [集合状.分次幺半群 𝒜] (decompose : A ->ₐ[R] ⨁ i, 𝒜 i)
  定义体: decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices decompose.comp (DirectSum.coeAlgHom 𝒜) = AlgHom.id _ _ from AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)

Depends on / 依赖: decompose
-/
abbrev GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose : A ->ₐ[R] ⨁ i, 𝒜 i)
    (right_inv : (DirectSum.coeAlgHom 𝒜).comp decompose = AlgHom.id R A)
    (left_inv : forall i (x : 𝒜 i), decompose (x : A) = DirectSum.of (fun i => ↥(𝒜 i)) i x) :
    GradedAlgebra 𝒜 where
  decompose' := decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices decompose.comp (DirectSum.coeAlgHom 𝒜) = AlgHom.id _ _ from AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)

instance (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]
    [i : GradedAlgebra 𝒜] : GradedAlgebra (𝒜 · |>.restrictScalars R₀) := { i with }

variable [GradedAlgebra 𝒜]

namespace DirectSum

-- We have to write the `@[simps]` lemmas by hand to see through the
-- `AlgEquiv.symm (decomposeAddEquiv 𝒜).symm`.
/--
Definition of `decomposeAlgEquiv` / `decomposeAlgEquiv` 的定义

English:
definition decomposeAlgEquiv
  signature: : A ≃ₐ[R] ⨁ i, 𝒜 i
  body: AlgEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := map_mul (coeAlgHom 𝒜)
      commutes' := (coeAlgHom 𝒜).commutes }

@[simp]

中文:
定义 decomposeAlgEquiv
  签名: : A ≃ₐ[R] ⨁ i, 𝒜 i
  定义体: AlgEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := map_mul (coeAlgHom 𝒜)
      commutes' := (coeAlgHom 𝒜).commutes }

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm, coeAlgHom, commutes, decomposeAddEquiv, map_mul
-/
def decomposeAlgEquiv : A ≃ₐ[R] ⨁ i, 𝒜 i :=
  AlgEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := map_mul (coeAlgHom 𝒜)
      commutes' := (coeAlgHom 𝒜).commutes }

@[simp]
/--
lemma `decomposeAlgEquiv_apply` / 引理 `decomposeAlgEquiv_apply`

English:
lemma decomposeAlgEquiv_apply
  given: (a : A)
  proof: rfl

@[simp]

中文:
引理 decomposeAlgEquiv_apply
  条件: (a : A)
  证明: rfl

@[simp]
-/
lemma decomposeAlgEquiv_apply (a : A) :
    decomposeAlgEquiv 𝒜 a = decompose 𝒜 a := rfl

@[simp]
/--
lemma `decomposeAlgEquiv_symm_apply` / 引理 `decomposeAlgEquiv_symm_apply`

English:
lemma decomposeAlgEquiv_symm_apply
  given: (a : ⨁ i, 𝒜 i)
  proof: rfl

@[simp]

中文:
引理 decomposeAlgEquiv_symm_apply
  条件: (a : ⨁ i, 𝒜 i)
  证明: rfl

@[simp]
-/
lemma decomposeAlgEquiv_symm_apply (a : ⨁ i, 𝒜 i) :
    (decomposeAlgEquiv 𝒜).symm a = (decompose 𝒜).symm a := rfl

@[simp]
/--
lemma `decompose_algebraMap` / 引理 `decompose_algebraMap`

English:
lemma decompose_algebraMap
  given: (r : R)
  proof: (decomposeAlgEquiv 𝒜).commutes r

@[simp]

中文:
引理 decompose_algebraMap
  条件: (r : R)
  证明: (decomposeAlgEquiv 𝒜).commutes r

@[simp]

Depends on / 依赖: commutes, decomposeAlgEquiv
-/
lemma decompose_algebraMap (r : R) :
    decompose 𝒜 (algebraMap R A r) = algebraMap R (⨁ i, 𝒜 i) r :=
  (decomposeAlgEquiv 𝒜).commutes r

@[simp]
/--
lemma `decompose_symm_algebraMap` / 引理 `decompose_symm_algebraMap`

English:
lemma decompose_symm_algebraMap
  given: (r : R)
  proof: (decomposeAlgEquiv 𝒜).symm.commutes r

中文:
引理 decompose_symm_algebraMap
  条件: (r : R)
  证明: (decomposeAlgEquiv 𝒜).symm.commutes r

Depends on / 依赖: commutes, decomposeAlgEquiv, symm.commutes
-/
lemma decompose_symm_algebraMap (r : R) :
    (decompose 𝒜).symm (algebraMap R (⨁ i, 𝒜 i) r) = algebraMap R A r :=
  (decomposeAlgEquiv 𝒜).symm.commutes r

end DirectSum

open DirectSum

/--
Definition of `GradedAlgebra.proj` / `GradedAlgebra.proj` 的定义

English:
definition GradedAlgebra.proj
  signature: (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜] (i : ι)
  body: (𝒜 i).subtype.comp (DFinsupp.lapply i).comp (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

@[simp]

中文:
定义 分次代数.proj
  签名: (𝒜 : ι -> 子模 R A) [分次代数 𝒜] (i : ι)
  定义体: (𝒜 i).subtype.comp (DFinsupp.lapply i).comp (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.lapply, decomposeAlgEquiv, lapply, subtype, subtype.comp, toAlgHom, toAlgHom.toLinearMap, toLinearMap
-/
def GradedAlgebra.proj (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A ->ₗ[R] A :=
(𝒜 i).subtype.comp (DFinsupp.lapply i).comp (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

@[simp]
/--
theorem `GradedAlgebra.proj_apply` / 定理 `GradedAlgebra.proj_apply`

English:
theorem GradedAlgebra.proj_apply
  given: (i : ι) (r : A)
  proof: rfl

中文:
定理 分次代数.proj_apply
  条件: (i : ι) (r : A)
  证明: rfl
-/
theorem GradedAlgebra.proj_apply (i : ι) (r : A) :
    GradedAlgebra.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl

/--
theorem `GradedAlgebra.proj_recompose` / 定理 `GradedAlgebra.proj_recompose`

English:
theorem GradedAlgebra.proj_recompose
  given: (a : ⨁ i, 𝒜 i) (i : ι)
  proof: by
  rw [GradedAlgebra.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

中文:
定理 分次代数.proj_recompose
  条件: (a : ⨁ i, 𝒜 i) (i : ι)
  证明: by
  rw [GradedAlgebra.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, GradedAlgebra, GradedAlgebra.proj_apply, apply_symm_apply, decompose_symm_of, proj_apply
-/
theorem GradedAlgebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedAlgebra.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (of _ i (a i)) := by
  rw [GradedAlgebra.proj_apply]; rw [decompose_symm_of]; rw [Equiv.apply_symm_apply]

/--
theorem `GradedAlgebra.mem_support_iff` / 定理 `GradedAlgebra.mem_support_iff`

English:
theorem GradedAlgebra.mem_support_iff
  given: [DecidableEq A] (r : A) (i : ι)
  proof: DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm

中文:
定理 分次代数.mem_support_iff
  条件: [DecidableEq A] (r : A) (i : ι)
  证明: DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_iff.trans, Submodule, Submodule.coe_eq_zero.not.symm, coe_eq_zero, mem_support_iff
-/
theorem GradedAlgebra.mem_support_iff [DecidableEq A] (r : A) (i : ι) :
    i in (decompose 𝒜 r).support ↔ GradedAlgebra.proj 𝒜 i r != 0 :=
  DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm

end GradedAlgebra

section CanonicalOrder

open SetLike.GradedMonoid DirectSum

variable [Semiring A] [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]

/-- If `A` is graded by a canonically ordered additive monoid, then the projection map `x ↦ x₀`
is a ring homomorphism.
-/
@[simps]
/--
Definition of `GradedRing.projZeroRingHom` / `GradedRing.projZeroRingHom` 的定义

English:
definition GradedRing.projZeroRingHom
  signature: : A ->+* A where
  body: decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn 𝒜 (fun x =>

中文:
定义 分次环.projZeroRingHom
  签名: : A ->+* A where
  定义体: decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn 𝒜 (fun x =>

Depends on / 依赖: decompose
-/
def GradedRing.projZeroRingHom : A ->+* A where
  toFun a := decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn 𝒜 (fun x => ?_) ?_ ?_
    · simp only [zero_mul, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rintro i ⟨c, hc⟩
      refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
      · simp only [mul_zero, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
      · rintro j ⟨c', hc'⟩
        simp only
        by_cases h : i + j = 0
        · rw [decompose_of_mem_same 𝒜
              (show c * c' in 𝒜 0 from h ▸ SetLike.GradedMul.mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c in 𝒜 0 from (add_eq_zero.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' in 𝒜 0 from (add_eq_zero.mp h).2 ▸ hc')]
        · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
          rcases show i != 0 ∨ j != 0 by rwa [add_eq_zero, not_and_or] at h with h' | h'
          · simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul]
          · simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero]
      · intro _ _ hd he
        simp only [mul_add, decompose_add, add_apply, AddMemClass.coe_add, hd, he]
    · rintro _ _ ha hb _
      simp only [add_mul, decompose_add, add_apply, AddMemClass.coe_add, ha, hb]

section GradeZero

/--
Definition of `GradedRing.projZeroRingHom'` / `GradedRing.projZeroRingHom'` 的定义

English:
definition GradedRing.projZeroRingHom'
  signature: : A ->+* 𝒜 0
  body: ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A ->+* SetLike.GradeZero.subsemiring 𝒜)

中文:
定义 分次环.projZeroRingHom'
  签名: : A ->+* 𝒜 0
  定义体: ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A ->+* SetLike.GradeZero.subsemiring 𝒜)

Depends on / 依赖: GradeZero, GradedRing, GradedRing.projZeroRingHom, SetLike, SetLike.GradeZero.subsemiring, SetLike.coe_mem, codRestrict, coe_mem, projZeroRingHom, subsemiring
-/
def GradedRing.projZeroRingHom' : A ->+* 𝒜 0 :=
  ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A ->+* SetLike.GradeZero.subsemiring 𝒜)

/--
lemma `GradedRing.coe_projZeroRingHom'_apply` / 引理 `GradedRing.coe_projZeroRingHom'_apply`

English:
lemma GradedRing.coe_projZeroRingHom'_apply
  given: (a : A)
  proof: rfl

中文:
引理 分次环.coe_projZeroRingHom'_apply
  条件: (a : A)
  证明: rfl
-/
@[simp] lemma GradedRing.coe_projZeroRingHom'_apply (a : A) :
    (GradedRing.projZeroRingHom' 𝒜 a : A) = GradedRing.projZeroRingHom 𝒜 a := rfl

/--
lemma `GradedRing.projZeroRingHom'_apply_coe` / 引理 `GradedRing.projZeroRingHom'_apply_coe`

English:
lemma GradedRing.projZeroRingHom'_apply_coe
  given: (a : 𝒜 0)
  proof: by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]

中文:
引理 分次环.projZeroRingHom'_apply_coe
  条件: (a : 𝒜 0)
  证明: by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]
-/
@[simp] lemma GradedRing.projZeroRingHom'_apply_coe (a : 𝒜 0) :
    GradedRing.projZeroRingHom' 𝒜 a = a := by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]

/--
lemma `GradedRing.projZeroRingHom'_surjective` / 引理 `GradedRing.projZeroRingHom'_surjective`

English:
lemma GradedRing.projZeroRingHom'_surjective
  proof: Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)

中文:
引理 分次环.projZeroRingHom'_surjective
  证明: Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)
-/
lemma GradedRing.projZeroRingHom'_surjective :
    Function.Surjective (GradedRing.projZeroRingHom' 𝒜) :=
  Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)

end GradeZero

variable {a b : A} {n i : ι}

namespace DirectSum

/--
theorem `coe_decompose_mul_of_left_mem_of_not_le` / 定理 `coe_decompose_mul_of_left_mem_of_not_le`

English:
theorem coe_decompose_mul_of_left_mem_of_not_le
  given: (a_mem : a in 𝒜 i) (h : ¬i <= n)
  proof: by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_not_le]

中文:
定理 coe_decompose_mul_of_left_mem_of_not_le
  条件: (a_mem : a in 𝒜 i) (h : ¬i <= n)
  证明: by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_not_le]

Depends on / 依赖: a_mem, coe_of_mul_apply_of_not_le, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_left_mem_of_not_le (a_mem : a in 𝒜 i) (h : ¬i <= n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_not_le]

/--
theorem `coe_decompose_mul_of_right_mem_of_not_le` / 定理 `coe_decompose_mul_of_right_mem_of_not_le`

English:
theorem coe_decompose_mul_of_right_mem_of_not_le
  given: (b_mem : b in 𝒜 i) (h : ¬i <= n)
  proof: by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_not_le]

中文:
定理 coe_decompose_mul_of_right_mem_of_not_le
  条件: (b_mem : b in 𝒜 i) (h : ¬i <= n)
  证明: by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_not_le]

Depends on / 依赖: b_mem, coe_mul_of_apply_of_not_le, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_right_mem_of_not_le (b_mem : b in 𝒜 i) (h : ¬i <= n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_not_le]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

/--
theorem `coe_decompose_mul_of_left_mem_of_le` / 定理 `coe_decompose_mul_of_left_mem_of_le`

English:
theorem coe_decompose_mul_of_left_mem_of_le
  given: (a_mem : a in 𝒜 i) (h : i <= n)
  proof: by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_le]

中文:
定理 coe_decompose_mul_of_left_mem_of_le
  条件: (a_mem : a in 𝒜 i) (h : i <= n)
  证明: by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_le]

Depends on / 依赖: a_mem, coe_of_mul_apply_of_le, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_left_mem_of_le (a_mem : a in 𝒜 i) (h : i <= n) :
    (decompose 𝒜 (a * b) n : A) = a * decompose 𝒜 b (n - i) := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_le]

/--
theorem `coe_decompose_mul_of_right_mem_of_le` / 定理 `coe_decompose_mul_of_right_mem_of_le`

English:
theorem coe_decompose_mul_of_right_mem_of_le
  given: (b_mem : b in 𝒜 i) (h : i <= n)
  proof: by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_le]

中文:
定理 coe_decompose_mul_of_right_mem_of_le
  条件: (b_mem : b in 𝒜 i) (h : i <= n)
  证明: by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_le]

Depends on / 依赖: b_mem, coe_mul_of_apply_of_le, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_right_mem_of_le (b_mem : b in 𝒜 i) (h : i <= n) :
    (decompose 𝒜 (a * b) n : A) = decompose 𝒜 a (n - i) * b := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_le]

/--
theorem `coe_decompose_mul_of_left_mem` / 定理 `coe_decompose_mul_of_left_mem`

English:
theorem coe_decompose_mul_of_left_mem
  given: (n) [Decidable (i <= n)] (a_mem : a in 𝒜 i)
  proof: by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply]

中文:
定理 coe_decompose_mul_of_left_mem
  条件: (n) [可判定 (i <= n)] (a_mem : a in 𝒜 i)
  证明: by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply]

Depends on / 依赖: a_mem, coe_of_mul_apply, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_left_mem (n) [Decidable (i <= n)] (a_mem : a in 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i <= n then a * decompose 𝒜 b (n - i) else 0 := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_of_mul_apply]

/--
theorem `coe_decompose_mul_of_right_mem` / 定理 `coe_decompose_mul_of_right_mem`

English:
theorem coe_decompose_mul_of_right_mem
  given: (n) [Decidable (i <= n)] (b_mem : b in 𝒜 i)
  proof: by
  lift b to 𝒜 i using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply]

中文:
定理 coe_decompose_mul_of_right_mem
  条件: (n) [可判定 (i <= n)] (b_mem : b in 𝒜 i)
  证明: by
  lift b to 𝒜 i using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply]

Depends on / 依赖: b_mem, coe_mul_of_apply, decompose_coe, decompose_mul
-/
theorem coe_decompose_mul_of_right_mem (n) [Decidable (i <= n)] (b_mem : b in 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i <= n then decompose 𝒜 a (n - i) * b else 0 := by
  lift b to 𝒜 i using b_mem
  rw [decompose_mul]; rw [decompose_coe]; rw [coe_mul_of_apply]

end DirectSum

end CanonicalOrder

namespace DirectSum.IsInternal

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {M : ι -> Submodule R A} [SetLike.GradedMonoid M]

-- The following lines were given on Zulip by Adam Topaz
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `coeAlgEquiv` / `coeAlgEquiv` 的定义

English:
definition coeAlgEquiv
  signature: (hM : DirectSum.IsInternal M)
  body: { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }

中文:
定义 coeAlgEquiv
  签名: (hM : 直和.Is整数ernal M)
  定义体: { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }

Depends on / 依赖: DirectSum, DirectSum.coeAlgHom, RingEquiv, RingEquiv.ofBijective, coeAlgHom, commutes, ofBijective
-/
noncomputable def coeAlgEquiv (hM : DirectSum.IsInternal M) :
    (DirectSum ι fun i => ↥(M i)) ≃ₐ[R] A :=
  { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }

/-- Given an `R`-algebra `A` and a family `ι → Submodule R A` of submodules
parameterized by an additive monoid `ι`
and satisfying `SetLike.GradedMonoid M` (essentially, is multiplicative)
such that `DirectSum.IsInternal M` (`A` is the direct sum of the `M i`),
we endow `A` with the structure of a graded algebra.
The submodules are the *homogeneous* parts. -/
@[instance_reducible]
/--
Definition of `gradedAlgebra` / `gradedAlgebra` 的定义

English:
definition gradedAlgebra
  signature: (hM : DirectSum.IsInternal M)
  body: { (inferInstance : SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgEquiv.symm
    left_inv := hM.coeAlgEquiv.symm.left_inv
    right_inv := hM.coeAlgEquiv.left_inv }

中文:
定义 gradedAlgebra
  签名: (hM : 直和.Is整数ernal M)
  定义体: { (inferInstance : SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgEquiv.symm
    left_inv := hM.coeAlgEquiv.symm.left_inv
    right_inv := hM.coeAlgEquiv.left_inv }

Depends on / 依赖: GradedMonoid, SetLike, SetLike.GradedMonoid, coeAlgEquiv, decompose, hM.coeAlgEquiv.left_inv, hM.coeAlgEquiv.symm, hM.coeAlgEquiv.symm.left_inv, left_inv, right_inv
-/
noncomputable def gradedAlgebra (hM : DirectSum.IsInternal M) : GradedAlgebra M :=
  { (inferInstance : SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgEquiv.symm
    left_inv := hM.coeAlgEquiv.symm.left_inv
    right_inv := hM.coeAlgEquiv.left_inv }

end DirectSum.IsInternal
