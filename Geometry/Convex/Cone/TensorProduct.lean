/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Tensor products of cones

Given ordered modules `M` and `N`, there are in general several distinct possible
orderings of the tensor product module `M ⊗ N`. Since the ordering of an ordered module
can be represented by its cone of nonnegative elements, there are likewise multiple
ways to construct a cone in `M ⊗ N` from cones in `M` and `N`. Such constructions
are referred to as tensor products of cones.

"Sufficiently nice" candidates for tensor products of cones are bounded by the minimal
and maximal tensor products. These products are generally distinct but coincide in special cases.

We define the minimal and maximal tensor products of pointed cones:

* `minTensorProduct C₁ C₂`: all conical combinations of elementary tensor products
  `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`.
* `maxTensorProduct C₁ C₂`: the dual cone of the minimal tensor product of the dual cones.

## Main results

* `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## Notation

* no special notation defined
* x, y, z are elements of the (original) cones
* φ, ψ are elements of the dual cones

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

@[expose] public section

open TensorProduct Module

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G : Type*} [AddCommGroup G] [Module R G]
variable {H : Type*} [AddCommGroup H] [Module R H]

namespace PointedCone

/--
Definition of `minTensorProduct` / `minTensorProduct` 的定义

English:
definition minTensorProduct
  signature: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  body: .hull R (.image2 (· otimesₜ[R] ·) C₁ C₂)

中文:
定义 minTensorProduct
  签名: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  定义体: .hull R (.image2 (· otimesₜ[R] ·) C₁ C₂)

Depends on / 依赖: image2
-/
noncomputable def minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G otimes[R] H) :=
  .hull R (.image2 (· otimesₜ[R] ·) C₁ C₂)

/--
Definition of `maxTensorProduct` / `maxTensorProduct` 的定义

English:
definition maxTensorProduct
  signature: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  body: .dual (dualDistrib R G H) (minTensorProduct (.dual (Dual.eval R G) C₁)
    (.dual (Dual.eval R H) C₂))

中文:
定义 maxTensorProduct
  签名: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  定义体: .dual (dualDistrib R G H) (minTensorProduct (.dual (Dual.eval R G) C₁)
    (.dual (Dual.eval R H) C₂))

Depends on / 依赖: Dual.eval, dualDistrib, minTensorProduct
-/
noncomputable def maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G otimes[R] H) :=
  .dual (dualDistrib R G H) (minTensorProduct (.dual (Dual.eval R G) C₁)
    (.dual (Dual.eval R H) C₂))

/-- Characterization of the maximal tensor product: `z` lies in `maxTensorProduct C₁ C₂` iff
all pairings with elementary dual tensors are nonnegative. -/
@[simp]
/--
theorem `mem_maxTensorProduct` / 定理 `mem_maxTensorProduct`

English:
theorem mem_maxTensorProduct
  given: {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G otimes[R] H}
  proof: by
  simp only [maxTensorProduct, minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual]

中文:
定理 mem_maxTensorProduct
  条件: {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G otimes[R] H}
  证明: by
  simp only [maxTensorProduct, minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual]
-/
theorem mem_maxTensorProduct {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G otimes[R] H} :
    z in maxTensorProduct (R := R) C₁ C₂ ↔
      forall φ in PointedCone.dual (Dual.eval R G) C₁,
      forall ψ in PointedCone.dual (Dual.eval R H) C₂,
      0 <= dualDistrib R G H (φ otimesₜ[R] ψ) z := by
  simp only [maxTensorProduct, minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual]

/--
theorem `tmul_mem_maxTensorProduct` / 定理 `tmul_mem_maxTensorProduct`

English:
theorem tmul_mem_maxTensorProduct
  statement: {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
  proof: by
  simp only [mem_maxTensorProduct, dualDistrib_apply]
  exact fun φ hφ ψ hψ => mul_nonneg (hφ hx) (hψ hy)

中文:
定理 tmul_mem_maxTensorProduct
  结论: {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
  证明: by
  simp only [mem_maxTensorProduct, dualDistrib_apply]
  exact fun φ hφ ψ hψ => mul_nonneg (hφ hx) (hψ hy)

Depends on / 依赖: dualDistrib_apply, mem_maxTensorProduct, mul_nonneg
-/
theorem tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
    (hy : y in C₂) : x otimesₜ[R] y in maxTensorProduct C₁ C₂ := by
  simp only [mem_maxTensorProduct, dualDistrib_apply]
  exact fun φ hφ ψ hψ => mul_nonneg (hφ hx) (hψ hy)

/--
theorem `tmul_mem_minTensorProduct` / 定理 `tmul_mem_minTensorProduct`

English:
theorem tmul_mem_minTensorProduct
  statement: {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
  proof: Submodule.subset_span (Set.mem_image2_of_mem hx hy)

中文:
定理 tmul_mem_minTensorProduct
  结论: {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
  证明: Submodule.subset_span (Set.mem_image2_of_mem hx hy)

Depends on / 依赖: Set.mem_image2_of_mem, Submodule, Submodule.subset_span, mem_image2_of_mem, subset_span
-/
theorem tmul_mem_minTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁)
    (hy : y in C₂) : x otimesₜ[R] y in minTensorProduct C₁ C₂ :=
  Submodule.subset_span (Set.mem_image2_of_mem hx hy)

/--
theorem `tmul_subset_maxTensorProduct` / 定理 `tmul_subset_maxTensorProduct`

English:
theorem tmul_subset_maxTensorProduct
  given: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  proof: fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_maxTensorProduct hx hy

中文:
定理 tmul_subset_maxTensorProduct
  条件: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  证明: fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_maxTensorProduct hx hy

Depends on / 依赖: tmul_mem_maxTensorProduct
-/
theorem tmul_subset_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· otimesₜ[R] ·) C₁ C₂ subseteq (maxTensorProduct C₁ C₂ : Set (G otimes[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_maxTensorProduct hx hy

/--
theorem `tmul_subset_minTensorProduct` / 定理 `tmul_subset_minTensorProduct`

English:
theorem tmul_subset_minTensorProduct
  given: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  proof: fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_minTensorProduct hx hy

中文:
定理 tmul_subset_minTensorProduct
  条件: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  证明: fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_minTensorProduct hx hy

Depends on / 依赖: tmul_mem_minTensorProduct
-/
theorem tmul_subset_minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· otimesₜ[R] ·) C₁ C₂ subseteq (minTensorProduct C₁ C₂ : Set (G otimes[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_minTensorProduct hx hy

/--
theorem `minTensorProduct_le_maxTensorProduct` / 定理 `minTensorProduct_le_maxTensorProduct`

English:
theorem minTensorProduct_le_maxTensorProduct
  given: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  proof: by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

中文:
定理 minTensorProduct_le_maxTensorProduct
  条件: (C₁ : PointedCone R G) (C₂ : PointedCone R H)
  证明: by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

Depends on / 依赖: Submodule, Submodule.span_le.mpr, span_le, tmul_subset_maxTensorProduct
-/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    minTensorProduct C₁ C₂ <= maxTensorProduct C₁ C₂ := by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

variable {C₁ C₁' : PointedCone R G} {C₂ C₂' : PointedCone R H} {z : G otimes[R] H}

/-- The minimal tensor product is commutative. -/
@[simp]
/--
theorem `minTensorProduct_comm` / 定理 `minTensorProduct_comm`

English:
theorem minTensorProduct_comm
  proof: by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_swap (· otimesₜ[R] · : H -> G -> _)]

中文:
定理 minTensorProduct_comm
  证明: by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_swap (· otimesₜ[R] · : H -> G -> _)]

Depends on / 依赖: Set.image2_swap, Set.image_image2, Submodule, Submodule.map_span, image2_swap, image_image2, map_span, minTensorProduct
-/
theorem minTensorProduct_comm :
    (minTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = minTensorProduct C₂ C₁ := by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_swap (· otimesₜ[R] · : H -> G -> _)]

/-- The maximal tensor product is commutative. -/
@[simp]
/--
theorem `maxTensorProduct_comm` / 定理 `maxTensorProduct_comm`

English:
theorem maxTensorProduct_comm
  proof: by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  refine ⟨?_, fun hz =>
    ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa [dualDistrib_apply_comm] using hw φ hφ ψ hψ
  · intro φ hφ ψ hψ
    simpa [dualDistrib_app

中文:
定理 maxTensorProduct_comm
  证明: by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  refine ⟨?_, fun hz =>
    ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa [dualDistrib_apply_comm] using hw φ hφ ψ hψ
  · intro φ hφ ψ hψ
    simpa [dualDistrib_app

Depends on / 依赖: TensorProduct, TensorProduct.comm, dualDistrib_apply_comm, mem_map, mem_maxTensorProduct, symm_apply_apply
-/
theorem maxTensorProduct_comm :
    (maxTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = maxTensorProduct C₂ C₁ := by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  refine ⟨?_, fun hz =>
    ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa [dualDistrib_apply_comm] using hw φ hφ ψ hψ
  · intro φ hφ ψ hψ
    simpa [dualDistrib_apply_comm] using hz ψ hψ φ hφ

/-- `minTensorProduct` is monotone. -/
@[gcongr]
/--
theorem `minTensorProduct_mono` / 定理 `minTensorProduct_mono`

English:
theorem minTensorProduct_mono
  given: (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂')
  proof: Submodule.span_mono Set.image2_subset h₁ h₂

中文:
定理 minTensorProduct_mono
  条件: (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂')
  证明: Submodule.span_mono Set.image2_subset h₁ h₂

Depends on / 依赖: Set.image2_subset, Submodule, Submodule.span_mono, image2_subset, span_mono
-/
theorem minTensorProduct_mono (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂') :
    minTensorProduct C₁ C₂ <= minTensorProduct C₁' C₂' :=
Submodule.span_mono Set.image2_subset h₁ h₂

/--
theorem `maxTensorProduct_mono` / 定理 `maxTensorProduct_mono`

English:
theorem maxTensorProduct_mono
  given: (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂')
  proof: fun _ hz => mem_maxTensorProduct.mpr fun φ hφ ψ hψ =>
    mem_maxTensorProduct.mp hz φ (dual_le_dual h₁ hφ) ψ (dual_le_dual h₂ hψ)

中文:
定理 maxTensorProduct_mono
  条件: (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂')
  证明: fun _ hz => mem_maxTensorProduct.mpr fun φ hφ ψ hψ =>
    mem_maxTensorProduct.mp hz φ (dual_le_dual h₁ hφ) ψ (dual_le_dual h₂ hψ)

Depends on / 依赖: dual_le_dual, mem_maxTensorProduct, mem_maxTensorProduct.mp, mem_maxTensorProduct.mpr
-/
theorem maxTensorProduct_mono (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂') :
    maxTensorProduct C₁ C₂ <= maxTensorProduct C₁' C₂' :=
  fun _ hz => mem_maxTensorProduct.mpr fun φ hφ ψ hψ =>
    mem_maxTensorProduct.mp hz φ (dual_le_dual h₁ hφ) ψ (dual_le_dual h₂ hψ)

variable {G' H' : Type*} [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/--
theorem `minTensorProduct_map_le` / 定理 `minTensorProduct_map_le`

English:
theorem minTensorProduct_map_le
  statement: (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
  proof: (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, h⟩ =>
    h ▸ map_tmul f g x y ▸ tmul_mem_minTensorProduct ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

中文:
定理 minTensorProduct_map_le
  结论: (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
  证明: (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, h⟩ =>
    h ▸ map_tmul f g x y ▸ tmul_mem_minTensorProduct ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

Depends on / 依赖: Submodule, Submodule.map_span_le, map_span_le, map_tmul, tmul_mem_minTensorProduct
-/
theorem minTensorProduct_map_le (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (minTensorProduct C₁ C₂).map (TensorProduct.map f g) <=
      minTensorProduct (C₁.map f) (C₂.map g) :=
  (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, h⟩ =>
    h ▸ map_tmul f g x y ▸ tmul_mem_minTensorProduct ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/--
theorem `maxTensorProduct_map_le` / 定理 `maxTensorProduct_map_le`

English:
theorem maxTensorProduct_map_le
  statement: (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
  proof: by
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, mem_maxTensorProduct] at hw ⊢
  intro φ hφ ψ hψ
  have h_eq : ((dualDistrib R G' H') (φ otimesₜ[R] ψ)).comp (TensorProduct.map f g) =
      ((dualDistrib R G H) ((φ.comp f) otimesₜ[R] (ψ.comp g))) :=
    TensorProduct.ext' fun x y => by simp [

中文:
定理 maxTensorProduct_map_le
  结论: (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
  证明: by
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, mem_maxTensorProduct] at hw ⊢
  intro φ hφ ψ hψ
  have h_eq : ((dualDistrib R G' H') (φ otimesₜ[R] ψ)).comp (TensorProduct.map f g) =
      ((dualDistrib R G H) ((φ.comp f) otimesₜ[R] (ψ.comp g))) :=
    TensorProduct.ext' fun x y => by simp [

Depends on / 依赖: DFunLike, DFunLike.congr_fun, SetLike, SetLike.mem_coe, TensorProduct, TensorProduct.ext, TensorProduct.map, congr_fun, convert, dualDistrib, h_eq, map_tmul, mem_coe, mem_maxTensorProduct
-/
theorem maxTensorProduct_map_le (f : G ->ₗ[R] G') (g : H ->ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (maxTensorProduct C₁ C₂).map (TensorProduct.map f g) <=
      maxTensorProduct (C₁.map f) (C₂.map g) := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, mem_maxTensorProduct] at hw ⊢
  intro φ hφ ψ hψ
  have h_eq : ((dualDistrib R G' H') (φ otimesₜ[R] ψ)).comp (TensorProduct.map f g) =
      ((dualDistrib R G H) ((φ.comp f) otimesₜ[R] (ψ.comp g))) :=
    TensorProduct.ext' fun x y => by simp [map_tmul]
  convert! hw (φ.comp f) (fun x hx => hφ ⟨x, hx, rfl⟩) (ψ.comp g) (fun y hy => hψ ⟨y, hy, rfl⟩)
  exact DFunLike.congr_fun h_eq w

end PointedCone
