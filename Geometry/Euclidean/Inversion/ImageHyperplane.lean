/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Image of a hyperplane under inversion

In this file we prove that the inversion with center `c` and radius `R ≠ 0` maps a sphere passing
through the center to a hyperplane, and vice versa. More precisely, it maps a sphere with center
`y ≠ c` and radius `dist y c` to the hyperplane
`AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R y)`.

The exact statements are a little more complicated because `EuclideanGeometry.inversion c R` sends
the center to itself, not to a point at infinity.

We also prove that the inversion sends an affine subspace passing through the center to itself.

## Keywords

inversion
-/

public section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] {c x y : P} {R : Real}

namespace EuclideanGeometry

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `inversion_mem_perpBisector_inversion_iff` / 定理 `inversion_mem_perpBisector_inversion_iff`

English:
theorem inversion_mem_perpBisector_inversion_iff
  given: (hR : R != 0) (hx : x != c) (hy : y != c)
  proof: by
  rw [mem_perpBisector_iff_dist_eq]; rw [dist_inversion_inversion hx hy]; rw [dist_inversion_center]
  simp [field, eq_comm, ↓hx, ↓hy]

中文:
定理 inversion_mem_perpBisector_inversion_iff
  条件: (hR : R != 0) (hx : x != c) (hy : y != c)
  证明: by
  rw [mem_perpBisector_iff_dist_eq]; rw [dist_inversion_inversion hx hy]; rw [dist_inversion_center]
  simp [field, eq_comm, ↓hx, ↓hy]

Depends on / 依赖: dist_inversion_center, dist_inversion_inversion, eq_comm, mem_perpBisector_iff_dist_eq
-/
theorem inversion_mem_perpBisector_inversion_iff (hR : R != 0) (hx : x != c) (hy : y != c) :
    inversion c R x in perpBisector c (inversion c R y) ↔ dist x y = dist y c := by
  rw [mem_perpBisector_iff_dist_eq]; rw [dist_inversion_inversion hx hy]; rw [dist_inversion_center]
  simp [field, eq_comm, ↓hx, ↓hy]

/--
theorem `inversion_mem_perpBisector_inversion_iff'` / 定理 `inversion_mem_perpBisector_inversion_iff'`

English:
theorem inversion_mem_perpBisector_inversion_iff'
  given: (hR : R != 0) (hy : y != c)
  proof: by
  rcases eq_or_ne x c with rfl | hx
  · simp [*]
  · simp [inversion_mem_perpBisector_inversion_iff hR hx hy, hx]

中文:
定理 inversion_mem_perpBisector_inversion_iff'
  条件: (hR : R != 0) (hy : y != c)
  证明: by
  rcases eq_or_ne x c with rfl | hx
  · simp [*]
  · simp [inversion_mem_perpBisector_inversion_iff hR hx hy, hx]

Depends on / 依赖: eq_or_ne, inversion_mem_perpBisector_inversion_iff
-/
theorem inversion_mem_perpBisector_inversion_iff' (hR : R != 0) (hy : y != c) :
    inversion c R x in perpBisector c (inversion c R y) ↔ dist x y = dist y c ∧ x != c := by
  rcases eq_or_ne x c with rfl | hx
  · simp [*]
  · simp [inversion_mem_perpBisector_inversion_iff hR hx hy, hx]

/--
theorem `preimage_inversion_perpBisector_inversion` / 定理 `preimage_inversion_perpBisector_inversion`

English:
theorem preimage_inversion_perpBisector_inversion
  given: (hR : R != 0) (hy : y != c)
  proof: Set.ext fun _ => inversion_mem_perpBisector_inversion_iff' hR hy

中文:
定理 preimage_inversion_perpBisector_inversion
  条件: (hR : R != 0) (hy : y != c)
  证明: Set.ext fun _ => inversion_mem_perpBisector_inversion_iff' hR hy

Depends on / 依赖: Set.ext, inversion_mem_perpBisector_inversion_iff
-/
theorem preimage_inversion_perpBisector_inversion (hR : R != 0) (hy : y != c) :
    inversion c R ⁻¹' perpBisector c (inversion c R y) = sphere y (dist y c) \ {c} :=
  Set.ext fun _ => inversion_mem_perpBisector_inversion_iff' hR hy

/--
theorem `preimage_inversion_perpBisector` / 定理 `preimage_inversion_perpBisector`

English:
theorem preimage_inversion_perpBisector
  given: (hR : R != 0) (hy : y != c)
  proof: by
  rw [← dist_inversion_center]; rw [← preimage_inversion_perpBisector_inversion hR]; rw [inversion_inversion] <;> simp [*]

中文:
定理 preimage_inversion_perpBisector
  条件: (hR : R != 0) (hy : y != c)
  证明: by
  rw [← dist_inversion_center]; rw [← preimage_inversion_perpBisector_inversion hR]; rw [inversion_inversion] <;> simp [*]

Depends on / 依赖: dist_inversion_center, inversion_inversion, preimage_inversion_perpBisector_inversion
-/
theorem preimage_inversion_perpBisector (hR : R != 0) (hy : y != c) :
    inversion c R ⁻¹' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  rw [← dist_inversion_center]; rw [← preimage_inversion_perpBisector_inversion hR]; rw [inversion_inversion] <;> simp [*]

/--
theorem `image_inversion_perpBisector` / 定理 `image_inversion_perpBisector`

English:
theorem image_inversion_perpBisector
  given: (hR : R != 0) (hy : y != c)
  proof: by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_perpBisector hR hy]

中文:
定理 image_inversion_perpBisector
  条件: (hR : R != 0) (hy : y != c)
  证明: by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_perpBisector hR hy]

Depends on / 依赖: image_eq_preimage_of_inverse, inversion_involutive, preimage_inversion_perpBisector
-/
theorem image_inversion_perpBisector (hR : R != 0) (hy : y != c) :
    inversion c R '' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_perpBisector hR hy]

/--
theorem `preimage_inversion_sphere_dist_center` / 定理 `preimage_inversion_sphere_dist_center`

English:
theorem preimage_inversion_sphere_dist_center
  given: (hR : R != 0) (hy : y != c)
  proof: by
  ext x
  rcases eq_or_ne x c with rfl | hx; · simp [dist_comm]
  rw [mem_preimage]; rw [mem_sphere]; rw [← inversion_mem_perpBisector_inversion_iff hR] <;> simp [*]

中文:
定理 preimage_inversion_sphere_dist_center
  条件: (hR : R != 0) (hy : y != c)
  证明: by
  ext x
  rcases eq_or_ne x c with rfl | hx; · simp [dist_comm]
  rw [mem_preimage]; rw [mem_sphere]; rw [← inversion_mem_perpBisector_inversion_iff hR] <;> simp [*]

Depends on / 依赖: dist_comm, eq_or_ne, inversion_mem_perpBisector_inversion_iff, mem_preimage, mem_sphere
-/
theorem preimage_inversion_sphere_dist_center (hR : R != 0) (hy : y != c) :
    inversion c R ⁻¹' sphere y (dist y c) =
      insert c (perpBisector c (inversion c R y) : Set P) := by
  ext x
  rcases eq_or_ne x c with rfl | hx; · simp [dist_comm]
  rw [mem_preimage]; rw [mem_sphere]; rw [← inversion_mem_perpBisector_inversion_iff hR] <;> simp [*]

/--
theorem `image_inversion_sphere_dist_center` / 定理 `image_inversion_sphere_dist_center`

English:
theorem image_inversion_sphere_dist_center
  given: (hR : R != 0) (hy : y != c)
  proof: by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_sphere_dist_center hR hy]

中文:
定理 image_inversion_sphere_dist_center
  条件: (hR : R != 0) (hy : y != c)
  证明: by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_sphere_dist_center hR hy]

Depends on / 依赖: image_eq_preimage_of_inverse, inversion_involutive, preimage_inversion_sphere_dist_center
-/
theorem image_inversion_sphere_dist_center (hR : R != 0) (hy : y != c) :
    inversion c R '' sphere y (dist y c) = insert c (perpBisector c (inversion c R y) : Set P) := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR)]; rw [preimage_inversion_sphere_dist_center hR hy]

/--
theorem `mapsTo_inversion_affineSubspace_of_mem` / 定理 `mapsTo_inversion_affineSubspace_of_mem`

English:
theorem mapsTo_inversion_affineSubspace_of_mem
  given: {p : AffineSubspace Real P} (hp : c in p)
  proof: fun _ => AffineMap.lineMap_mem _ hp

中文:
定理 mapsTo_inversion_affineSubspace_of_mem
  条件: {p : AffineSubspace 实数 P} (hp : c in p)
  证明: fun _ => AffineMap.lineMap_mem _ hp

Depends on / 依赖: AffineMap, AffineMap.lineMap_mem, lineMap_mem
-/
theorem mapsTo_inversion_affineSubspace_of_mem {p : AffineSubspace Real P} (hp : c in p) :
    MapsTo (inversion c R) p p := fun _ => AffineMap.lineMap_mem _ hp

/--
theorem `image_inversion_affineSubspace_of_mem` / 定理 `image_inversion_affineSubspace_of_mem`

English:
theorem image_inversion_affineSubspace_of_mem
  given: {p : AffineSubspace Real P} (hR : R != 0) (hp : c in p)
  proof: (mapsTo_inversion_affineSubspace_of_mem hp).image_subset.antisymm fun x hx =>
    ⟨inversion c R x, mapsTo_inversion_affineSubspace_of_mem hp hx, inversion_inversion _ hR _⟩

中文:
定理 image_inversion_affineSubspace_of_mem
  条件: {p : AffineSubspace 实数 P} (hR : R != 0) (hp : c in p)
  证明: (mapsTo_inversion_affineSubspace_of_mem hp).image_subset.antisymm fun x hx =>
    ⟨inversion c R x, mapsTo_inversion_affineSubspace_of_mem hp hx, inversion_inversion _ hR _⟩

Depends on / 依赖: antisymm, image_subset, image_subset.antisymm, inversion, inversion_inversion, mapsTo_inversion_affineSubspace_of_mem
-/
theorem image_inversion_affineSubspace_of_mem {p : AffineSubspace Real P} (hR : R != 0) (hp : c in p) :
    inversion c R '' p = p :=
  (mapsTo_inversion_affineSubspace_of_mem hp).image_subset.antisymm fun x hx =>
    ⟨inversion c R x, mapsTo_inversion_affineSubspace_of_mem hp hx, inversion_inversion _ hR _⟩

end EuclideanGeometry
