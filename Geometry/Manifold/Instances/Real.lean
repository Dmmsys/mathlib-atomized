/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`, and prove that its boundary is indeed `{x, y}`
whenever `x < y`. As a corollary, a product `M × [x, y]` with a manifold `M` without boundary
has boundary `M × {x, y}`.

More specifically, we introduce
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notation

In the scope `Manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `EuclideanSpace ℝ (Fin n)`
* `𝓡∂ n` for `modelWithCornersEuclideanHalfSpace n`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `EuclideanSpace ℝ (Fin m)`,
and `N` is smooth with boundary modelled on `EuclideanHalfSpace n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners cannot be implicit, see the discussion in
`Geometry.Manifold.IsManifold`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[Fact (x < y)]`.
-/

@[expose] public section

noncomputable section

open Set Function WithLp

open scoped Manifold ContDiff ENNReal

/-- The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
@[implicit_reducible, wikidata Q644719]
/--
Definition of `EuclideanHalfSpace` / `EuclideanHalfSpace` 的定义

English:
definition EuclideanHalfSpace
  signature: (n : Nat) [NeZero n]
  body: { x : EuclideanSpace Real (Fin n) // 0 <= x 0 }
deriving TopologicalSpace

中文:
定义 EuclideanHalfSpace
  签名: (n : 自然数) [NeZero n]
  定义体: { x : EuclideanSpace Real (Fin n) // 0 <= x 0 }
deriving TopologicalSpace

Depends on / 依赖: EuclideanSpace
-/
def EuclideanHalfSpace (n : Nat) [NeZero n] : Type :=
  { x : EuclideanSpace Real (Fin n) // 0 <= x 0 }
deriving TopologicalSpace

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
@[implicit_reducible]
/--
Definition of `EuclideanQuadrant` / `EuclideanQuadrant` 的定义

English:
definition EuclideanQuadrant
  signature: (n : Nat)
  body: { x : EuclideanSpace Real (Fin n) // forall i : Fin n, 0 <= x i }
deriving TopologicalSpace

中文:
定义 EuclideanQuadrant
  签名: (n : 自然数)
  定义体: { x : EuclideanSpace Real (Fin n) // forall i : Fin n, 0 <= x i }
deriving TopologicalSpace

Depends on / 依赖: EuclideanSpace
-/
def EuclideanQuadrant (n : Nat) : Type :=
  { x : EuclideanSpace Real (Fin n) // forall i : Fin n, 0 <= x i }
deriving TopologicalSpace

section

/- Register class instances for Euclidean half-space and quadrant, that cannot be noticed
without the following reducibility attribute (which is only set in this section). -/

variable {n : Nat}

instance {n : Nat} [NeZero n] : Zero (EuclideanHalfSpace n) := ⟨⟨0, by simp⟩⟩

instance {n : Nat} : Zero (EuclideanQuadrant n) := ⟨⟨0, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] : Inhabited (EuclideanHalfSpace n)
  body: ⟨0⟩

中文:
实例 [NeZero
  签名: n] : 可居 (EuclideanHalfSpace n)
  定义体: ⟨0⟩
-/
instance [NeZero n] : Inhabited (EuclideanHalfSpace n) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (EuclideanQuadrant n)
  body: ⟨0⟩

@[ext]

中文:
实例 :
  签名: 可居 (EuclideanQuadrant n)
  定义体: ⟨0⟩

@[ext]
-/
instance : Inhabited (EuclideanQuadrant n) :=
  ⟨0⟩

@[ext]
/--
theorem `EuclideanQuadrant.ext` / 定理 `EuclideanQuadrant.ext`

English:
theorem EuclideanQuadrant.ext
  given: (x y : EuclideanQuadrant n) (h : x.1 = y.1)
  statement: x = y
  proof: Subtype.ext h

@[ext]

中文:
定理 EuclideanQuadrant.ext
  条件: (x y : EuclideanQuadrant n) (h : x.1 = y.1)
  结论: x = y
  证明: Subtype.ext h

@[ext]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem EuclideanQuadrant.ext (x y : EuclideanQuadrant n) (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[ext]
/--
theorem `EuclideanHalfSpace.ext` / 定理 `EuclideanHalfSpace.ext`

English:
theorem EuclideanHalfSpace.ext
  statement: [NeZero n] (x y : EuclideanHalfSpace n)
  proof: Subtype.ext h

中文:
定理 EuclideanHalfSpace.ext
  结论: [NeZero n] (x y : EuclideanHalfSpace n)
  证明: Subtype.ext h

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem EuclideanHalfSpace.ext [NeZero n] (x y : EuclideanHalfSpace n)
    (h : x.1 = y.1) : x = y :=
  Subtype.ext h

/--
theorem `EuclideanHalfSpace.convex` / 定理 `EuclideanHalfSpace.convex`

English:
theorem EuclideanHalfSpace.convex
  given: [NeZero n]
  proof: fun _ hx _ hy _ _ _ _ _ => by dsimp at hx hy ⊢; positivity

中文:
定理 EuclideanHalfSpace.convex
  条件: [NeZero n]
  证明: fun _ hx _ hy _ _ _ _ _ => by dsimp at hx hy ⊢; positivity
-/
theorem EuclideanHalfSpace.convex [NeZero n] :
    Convex Real { x : EuclideanSpace Real (Fin n) | 0 <= x 0 } :=
  fun _ hx _ hy _ _ _ _ _ => by dsimp at hx hy ⊢; positivity

/--
theorem `EuclideanQuadrant.convex` / 定理 `EuclideanQuadrant.convex`

English:
theorem EuclideanQuadrant.convex
  proof: fun _ hx _ hy _ _ _ _ _ i => by dsimp at hx hy ⊢; specialize hx i; specialize hy i; positivity

中文:
定理 EuclideanQuadrant.convex
  证明: fun _ hx _ hy _ _ _ _ _ i => by dsimp at hx hy ⊢; specialize hx i; specialize hy i; positivity

Depends on / 依赖: specialize
-/
theorem EuclideanQuadrant.convex :
    Convex Real { x : EuclideanSpace Real (Fin n) | forall i, 0 <= x i } :=
  fun _ hx _ hy _ _ _ _ _ i => by dsimp at hx hy ⊢; specialize hx i; specialize hy i; positivity

/--
Instance `EuclideanHalfSpace.pathConnectedSpace` / 实例 `EuclideanHalfSpace.pathConnectedSpace`

English:
instance EuclideanHalfSpace.pathConnectedSpace
  signature: [NeZero n]
  body: isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

中文:
实例 EuclideanHalfSpace.pathConnectedSpace
  签名: [NeZero n]
  定义体: isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

Depends on / 依赖: convex, convex.isPathConnected, isPathConnected, isPathConnected_iff_pathConnectedSpace, isPathConnected_iff_pathConnectedSpace.mp
-/
instance EuclideanHalfSpace.pathConnectedSpace [NeZero n] :
    PathConnectedSpace (EuclideanHalfSpace n) :=
isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

/--
Instance `EuclideanQuadrant.pathConnectedSpace` / 实例 `EuclideanQuadrant.pathConnectedSpace`

English:
instance EuclideanQuadrant.pathConnectedSpace
  signature: : PathConnectedSpace (EuclideanQuadrant n)
  body: isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

中文:
实例 EuclideanQuadrant.pathConnectedSpace
  签名: : 道路连通空间 (EuclideanQuadrant n)
  定义体: isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

Depends on / 依赖: convex, convex.isPathConnected, isPathConnected, isPathConnected_iff_pathConnectedSpace, isPathConnected_iff_pathConnectedSpace.mp
-/
instance EuclideanQuadrant.pathConnectedSpace : PathConnectedSpace (EuclideanQuadrant n) :=
isPathConnected_iff_pathConnectedSpace.mp convex.isPathConnected ⟨0, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] : LocallyPathConnectedSpace (EuclideanHalfSpace n)
  body: EuclideanHalfSpace.convex.locallyPathConnectedSpace

中文:
实例 [NeZero
  签名: n] : LocallyPathConnected空间 (EuclideanHalfSpace n)
  定义体: EuclideanHalfSpace.convex.locallyPathConnectedSpace

Depends on / 依赖: EuclideanHalfSpace, EuclideanHalfSpace.convex.locallyPathConnectedSpace, convex, locallyPathConnectedSpace
-/
instance [NeZero n] : LocallyPathConnectedSpace (EuclideanHalfSpace n) :=
  EuclideanHalfSpace.convex.locallyPathConnectedSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyPathConnectedSpace (EuclideanQuadrant n)
  body: EuclideanQuadrant.convex.locallyPathConnectedSpace

中文:
实例 :
  签名: LocallyPathConnected空间 (EuclideanQuadrant n)
  定义体: EuclideanQuadrant.convex.locallyPathConnectedSpace

Depends on / 依赖: EuclideanQuadrant, EuclideanQuadrant.convex.locallyPathConnectedSpace, convex, locallyPathConnectedSpace
-/
instance : LocallyPathConnectedSpace (EuclideanQuadrant n) :=
  EuclideanQuadrant.convex.locallyPathConnectedSpace

/--
theorem `range_euclideanHalfSpace` / 定理 `range_euclideanHalfSpace`

English:
theorem range_euclideanHalfSpace
  given: (n : Nat) [NeZero n]
  proof: Subtype.range_val

@[simp]

中文:
定理 range_euclideanHalfSpace
  条件: (n : 自然数) [NeZero n]
  证明: Subtype.range_val

@[simp]

Depends on / 依赖: Subtype, Subtype.range_val, range_val
-/
theorem range_euclideanHalfSpace (n : Nat) [NeZero n] :
    range (Subtype.val : EuclideanHalfSpace n -> _) = { y | 0 <= y 0 } :=
  Subtype.range_val

@[simp]
/--
theorem `interior_halfSpace` / 定理 `interior_halfSpace`

English:
theorem interior_halfSpace
  given: {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n)
  proof: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage]; rw [interior_Ici]
  fun_prop

@[simp]

中文:
定理 interior_halfSpace
  条件: {n : 自然数} (p : 实数>=0∞) (a : 实数) (i : 有限集 n)
  证明: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage]; rw [interior_Ici]
  fun_prop

@[simp]

Depends on / 依赖: PiLp.isOpenMap_apply, fun_prop, interior, interior_Ici, isOpenMap_apply, preimage_interior_eq_interior_preimage
-/
theorem interior_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) :
    interior { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a < y i } := by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage]; rw [interior_Ici]
  fun_prop

@[simp]
/--
theorem `closure_halfSpace` / 定理 `closure_halfSpace`

English:
theorem closure_halfSpace
  given: {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n)
  proof: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ici]
  fun_prop

@[simp]

中文:
定理 closure_halfSpace
  条件: {n : 自然数} (p : 实数>=0∞) (a : 实数) (i : 有限集 n)
  证明: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ici]
  fun_prop

@[simp]

Depends on / 依赖: PiLp.isOpenMap_apply, closure, closure_Ici, fun_prop, isOpenMap_apply, preimage_closure_eq_closure_preimage
-/
theorem closure_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a <= y i } := by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ici]
  fun_prop

@[simp]
/--
theorem `closure_open_halfSpace` / 定理 `closure_open_halfSpace`

English:
theorem closure_open_halfSpace
  given: {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n)
  proof: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ioi]
  fun_prop

@[simp]

中文:
定理 closure_open_halfSpace
  条件: {n : 自然数} (p : 实数>=0∞) (a : 实数) (i : 有限集 n)
  证明: by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ioi]
  fun_prop

@[simp]

Depends on / 依赖: PiLp.isOpenMap_apply, closure, closure_Ioi, fun_prop, isOpenMap_apply, preimage_closure_eq_closure_preimage
-/
theorem closure_open_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n => Real) | a < y i } = { y | a <= y i } := by
  let f : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage]; rw [closure_Ioi]
  fun_prop

@[simp]
/--
theorem `frontier_halfSpace` / 定理 `frontier_halfSpace`

English:
theorem frontier_halfSpace
  given: {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n)
  proof: by
  rw [frontier]; rw [closure_halfSpace]; rw [interior_halfSpace]
  ext y
  simpa only [mem_sdiff, mem_ofPred_eq, not_lt] using antisymm_iff

中文:
定理 frontier_halfSpace
  条件: {n : 自然数} (p : 实数>=0∞) (a : 实数) (i : 有限集 n)
  证明: by
  rw [frontier]; rw [closure_halfSpace]; rw [interior_halfSpace]
  ext y
  simpa only [mem_sdiff, mem_ofPred_eq, not_lt] using antisymm_iff

Depends on / 依赖: antisymm_iff, closure_halfSpace, frontier, interior_halfSpace, mem_ofPred_eq, mem_sdiff, not_lt
-/
theorem frontier_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) :
    frontier { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a = y i } := by
  rw [frontier]; rw [closure_halfSpace]; rw [interior_halfSpace]
  ext y
  simpa only [mem_sdiff, mem_ofPred_eq, not_lt] using antisymm_iff
/--
theorem `range_euclideanQuadrant` / 定理 `range_euclideanQuadrant`

English:
theorem range_euclideanQuadrant
  given: (n : Nat)
  proof: Subtype.range_val

中文:
定理 range_euclideanQuadrant
  条件: (n : 自然数)
  证明: Subtype.range_val

Depends on / 依赖: Subtype, Subtype.range_val, range_val
-/
theorem range_euclideanQuadrant (n : Nat) :
    range (Subtype.val : EuclideanQuadrant n -> _) = { y | forall i : Fin n, 0 <= y i } :=
  Subtype.range_val

/--
theorem `interior_euclideanQuadrant` / 定理 `interior_euclideanQuadrant`

English:
theorem interior_euclideanQuadrant
  given: (n : Nat) (p : Real>=0∞) (a : Real)
  proof: by
  let f i : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  have h : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a <= y i } = ⋂ i, (f i) ⁻¹' Ici a := by
    ext; simp; rfl
  have h' : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a < y i } = ⋂ i, (f i) ⁻¹' Ioi a :

中文:
定理 interior_euclideanQuadrant
  条件: (n : 自然数) (p : 实数>=0∞) (a : 实数)
  证明: by
  let f i : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  have h : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a <= y i } = ⋂ i, (f i) ⁻¹' Ici a := by
    ext; simp; rfl
  have h' : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a < y i } = ⋂ i, (f i) ⁻¹' Ioi a :

Depends on / 依赖: PiLp.isOpenMap_apply, fun_prop, iInter_congr, interior_Ici, interior_iInter_of_finite, isOpenMap_apply, preimage_interior_eq_interior_preimage
-/
theorem interior_euclideanQuadrant (n : Nat) (p : Real>=0∞) (a : Real) :
    interior { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a <= y i } =
      { y | forall i : Fin n, a < y i } := by
  let f i : PiLp p (fun _ : Fin n => Real) -> Real := fun x => x i
  have h : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a <= y i } = ⋂ i, (f i) ⁻¹' Ici a := by
    ext; simp; rfl
  have h' : { y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a < y i } = ⋂ i, (f i) ⁻¹' Ioi a := by
    ext; simp; rfl
  rw [h]; rw [h']; rw [interior_iInter_of_finite]
  apply iInter_congr fun i => ?_
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage]; rw [interior_Ici]
  fun_prop

end

/--
Definition of `modelWithCornersEuclideanHalfSpace` / `modelWithCornersEuclideanHalfSpace` 的定义

English:
definition modelWithCornersEuclideanHalfSpace
  signature: (n : Nat) [NeZero n]
  body: Subtype.val
  invFun x := ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩
  source := univ
  target := { x | 0 <= x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk]; rw [← WithLp.equiv_symm_apply]; rw [Equiv.symm_appl

中文:
定义 modelWithCornersEuclideanHalfSpace
  签名: (n : 自然数) [NeZero n]
  定义体: Subtype.val
  invFun x := ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩
  source := univ
  target := { x | 0 <= x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk]; rw [← WithLp.equiv_symm_apply]; rw [Equiv.symm_appl

Depends on / 依赖: Subtype, Subtype.val
-/
def modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] :
    ModelWithCorners Real (EuclideanSpace Real (Fin n)) (EuclideanHalfSpace n) where
  toFun := Subtype.val
  invFun x := ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩
  source := univ
  target := { x | 0 <= x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk]; rw [← WithLp.equiv_symm_apply]; rw [Equiv.symm_apply_eq]; rw [update_eq_iff]
    exact ⟨max_eq_left xprop, fun i _ => rfl⟩
  right_inv' _ hx := by
    rw [Subtype.coe_mk]; rw [← WithLp.equiv_symm_apply]; rw [Equiv.symm_apply_eq]; rw [update_eq_iff]
    exact ⟨max_eq_left hx, fun _ _ => rfl⟩
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte]
    apply Convex.convex_isRCLikeNormedField
    rw [range_euclideanHalfSpace n]
    exact EuclideanHalfSpace.convex (n := n)
  nonempty_interior' := by
    rw [range_euclideanHalfSpace]; rw [interior_halfSpace]
    exact ⟨toLp 2 fun i => 1, by simp⟩
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by
    exact ((PiLp.continuous_toLp 2 _).comp <| (PiLp.continuous_ofLp 2 _).update 0 <|
      (PiLp.continuous_apply 2 _ 0).max continuous_const).subtype_mk _

/--
Definition of `modelWithCornersEuclideanQuadrant` / `modelWithCornersEuclideanQuadrant` 的定义

English:
definition modelWithCornersEuclideanQuadrant
  signature: (n : Nat)
  body: Subtype.val
  invFun x := ⟨toLp 2 fun i => max (x i) 0,
    fun i => by simp only [le_sup_right]⟩
  source := univ
  target := { x | forall i, 0 <= x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [x.2 i, sup_of_le_left]
  right_inv' x hx :

中文:
定义 modelWithCornersEuclideanQuadrant
  签名: (n : 自然数)
  定义体: Subtype.val
  invFun x := ⟨toLp 2 fun i => max (x i) 0,
    fun i => by simp only [le_sup_right]⟩
  source := univ
  target := { x | forall i, 0 <= x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [x.2 i, sup_of_le_left]
  right_inv' x hx :

Depends on / 依赖: Subtype, Subtype.val
-/
def modelWithCornersEuclideanQuadrant (n : Nat) :
    ModelWithCorners Real (EuclideanSpace Real (Fin n)) (EuclideanQuadrant n) where
  toFun := Subtype.val
  invFun x := ⟨toLp 2 fun i => max (x i) 0,
    fun i => by simp only [le_sup_right]⟩
  source := univ
  target := { x | forall i, 0 <= x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [x.2 i, sup_of_le_left]
  right_inv' x hx := by ext1 i; simp only [hx i, sup_of_le_left]
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte]
    apply Convex.convex_isRCLikeNormedField
    rw [range_euclideanQuadrant]
    exact EuclideanQuadrant.convex
  nonempty_interior' := by
    rw [range_euclideanQuadrant]; rw [interior_euclideanQuadrant]
    exact ⟨toLp 2 fun i => 1, by simp⟩
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp <|
    (continuous_pi fun i => ((PiLp.continuous_apply 2 _ i).max continuous_const))) _

/-- The model space used to define `n`-dimensional real manifolds without boundary. -/
scoped[Manifold]
  notation3 "𝓡 " n =>
    (modelWithCornersSelf Real (EuclideanSpace Real (Fin n)) :
      ModelWithCorners Real (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)))

/-- The model space used to define `n`-dimensional real manifolds with boundary. -/
scoped[Manifold]
  notation3 "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners Real (EuclideanSpace Real (Fin n)) (EuclideanHalfSpace n))

/--
lemma `modelWithCornersEuclideanHalfSpace_toFun` / 引理 `modelWithCornersEuclideanHalfSpace_toFun`

English:
lemma modelWithCornersEuclideanHalfSpace_toFun
  given: (n : Nat) [NeZero n]
  proof: rfl

中文:
引理 modelWithCornersEuclideanHalfSpace_toFun
  条件: (n : 自然数) [NeZero n]
  证明: rfl
-/
@[simp] lemma modelWithCornersEuclideanHalfSpace_toFun (n : Nat) [NeZero n] :
    (𝓡∂ n : _ -> _) = Subtype.val := rfl

/--
lemma `modelWithCornersEuclideanHalfSpace_symm_apply` / 引理 `modelWithCornersEuclideanHalfSpace_symm_apply`

English:
lemma modelWithCornersEuclideanHalfSpace_symm_apply
  statement: {n : Nat} [NeZero n]
  proof: rfl

中文:
引理 modelWithCornersEuclideanHalfSpace_symm_apply
  结论: {n : 自然数} [NeZero n]
  证明: rfl
-/
lemma modelWithCornersEuclideanHalfSpace_symm_apply {n : Nat} [NeZero n]
    (x : EuclideanSpace Real (Fin n)) :
    (𝓡∂ n).symm x = ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩ := rfl

/--
lemma `modelWithCornersEuclideanHalfSpace_zero` / 引理 `modelWithCornersEuclideanHalfSpace_zero`

English:
lemma modelWithCornersEuclideanHalfSpace_zero
  given: {n : Nat} [NeZero n]
  statement: (𝓡∂ n) 0 = 0
  proof: rfl

中文:
引理 modelWithCornersEuclideanHalfSpace_zero
  条件: {n : 自然数} [NeZero n]
  结论: (𝓡∂ n) 0 = 0
  证明: rfl
-/
lemma modelWithCornersEuclideanHalfSpace_zero {n : Nat} [NeZero n] : (𝓡∂ n) 0 = 0 := rfl

/--
lemma `range_modelWithCornersEuclideanHalfSpace` / 引理 `range_modelWithCornersEuclideanHalfSpace`

English:
lemma range_modelWithCornersEuclideanHalfSpace
  given: (n : Nat) [NeZero n]
  proof: range_euclideanHalfSpace n

中文:
引理 range_modelWithCornersEuclideanHalfSpace
  条件: (n : 自然数) [NeZero n]
  证明: range_euclideanHalfSpace n

Depends on / 依赖: range_euclideanHalfSpace
-/
lemma range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] :
    range (𝓡∂ n) = { y | 0 <= y 0 } := range_euclideanHalfSpace n

/--
lemma `interior_range_modelWithCornersEuclideanHalfSpace` / 引理 `interior_range_modelWithCornersEuclideanHalfSpace`

English:
lemma interior_range_modelWithCornersEuclideanHalfSpace
  given: (n : Nat) [NeZero n]
  proof: by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 <= y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _

中文:
引理 interior_range_modelWithCornersEuclideanHalfSpace
  条件: (n : 自然数) [NeZero n]
  证明: by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 <= y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _

Depends on / 依赖: interior, interior_halfSpace, range_euclideanHalfSpace
-/
lemma interior_range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] :
    interior (range (𝓡∂ n)) = { y | 0 < y 0 } := by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 <= y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _

/--
lemma `frontier_range_modelWithCornersEuclideanHalfSpace` / 引理 `frontier_range_modelWithCornersEuclideanHalfSpace`

English:
lemma frontier_range_modelWithCornersEuclideanHalfSpace
  given: (n : Nat) [NeZero n]
  proof: by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 <= y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _

中文:
引理 frontier_range_modelWithCornersEuclideanHalfSpace
  条件: (n : 自然数) [NeZero n]
  证明: by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 <= y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _

Depends on / 依赖: frontier, frontier_halfSpace, range_euclideanHalfSpace
-/
lemma frontier_range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] :
    frontier (range (𝓡∂ n)) = { y | 0 = y 0 } := by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 <= y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _

/--
Definition of `IccLeftChart` / `IccLeftChart` 的定义

English:
definition IccLeftChart
  signature: (x y : Real) [h : Fact (x < y)]
  body: { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨toLp 2 fun _ => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩
  map_source' := by simp
  map_target' := by
    simp only [mi

中文:
定义 IccLeftChart
  签名: (x y : 实数) [h : Fact (x < y)]
  定义体: { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨toLp 2 fun _ => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩
  map_source' := by simp
  map_target' := by
    simp only [mi

Depends on / 依赖: z.val
-/
def IccLeftChart (x y : Real) [h : Fact (x < y)] :
    OpenPartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨toLp 2 fun _ => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩
  map_source' := by simp
  map_target' := by
    simp only [min_lt_iff, mem_ofPred_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_ofPred_eq, mem_Icc] at hz h'z
    simp only [Fin.isValue, sub_add_cancel, hz, inf_of_le_left]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    ext i
    dsimp at hz h'z
    have A : x + z 0 <= y := by linarith
    rw [Subsingleton.elim i 0]
    simp only [Fin.isValue, add_comm, A, inf_of_le_left, add_sub_cancel_left]
  open_source :=
    haveI : IsOpen { z : Real | z < y } := isOpen_Iio
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : Real | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace Real (Fin 1) | z 0 < y - x } :=
      this.preimage (@PiLp.continuous_apply 2 (Fin 1) (fun _ => Real) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

variable {x y : Real} [hxy : Fact (x < y)]

/--
lemma `IccLeftChart_apply` / 引理 `IccLeftChart_apply`

English:
lemma IccLeftChart_apply
  given: (z : Icc x y)
  proof: rfl

中文:
引理 IccLeftChart_apply
  条件: (z : 闭区间 x y)
  证明: rfl
-/
lemma IccLeftChart_apply (z : Icc x y) :
    IccLeftChart x y z = ⟨toLp 2 fun _ => z.val - x, by aesop⟩ :=
  rfl

/--
lemma `IccLeftChart_symm_apply` / 引理 `IccLeftChart_symm_apply`

English:
lemma IccLeftChart_symm_apply
  given: (x y : Real) [h : Fact (x < y)] (z : EuclideanHalfSpace 1)
  proof: rfl

中文:
引理 IccLeftChart_symm_apply
  条件: (x y : 实数) [h : Fact (x < y)] (z : EuclideanHalfSpace 1)
  证明: rfl
-/
lemma IccLeftChart_symm_apply (x y : Real) [h : Fact (x < y)] (z : EuclideanHalfSpace 1) :
    (IccLeftChart x y).symm z = ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩ :=
  rfl

/--
lemma `IccLeftChart_symm_apply_of_le` / 引理 `IccLeftChart_symm_apply_of_le`

English:
lemma IccLeftChart_symm_apply_of_le
  given: {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x)
  proof: by
  ext
  simp only [IccLeftChart_symm_apply, inf_eq_left]
  linarith

中文:
引理 IccLeftChart_symm_apply_of_le
  条件: {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x)
  证明: by
  ext
  simp only [IccLeftChart_symm_apply, inf_eq_left]
  linarith

Depends on / 依赖: IccLeftChart_symm_apply, inf_eq_left
-/
lemma IccLeftChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x) :
    (IccLeftChart x y).symm z =
      ⟨z.val 0 + x, by simpa [z.prop, hxy.out.le, ← le_add_neg_iff_add_le]⟩ := by
  ext
  simp only [IccLeftChart_symm_apply, inf_eq_left]
  linarith

namespace Fact.Manifold

scoped instance : Fact (x <= y) := Fact.mk hxy.out.le

end Fact.Manifold

open Fact.Manifold

/--
lemma `IccLeftChart_extend_bot` / 引理 `IccLeftChart_extend_bot`

English:
lemma IccLeftChart_extend_bot
  statement: (IccLeftChart x y).extend (𝓡∂ 1) ⊥ = 0
  proof: by
  norm_num [IccLeftChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

中文:
引理 IccLeftChart_extend_bot
  结论: (IccLeftChart x y).extend (𝓡∂ 1) ⊥ = 0
  证明: by
  norm_num [IccLeftChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

Depends on / 依赖: IccLeftChart, modelWithCornersEuclideanHalfSpace_zero
-/
lemma IccLeftChart_extend_bot : (IccLeftChart x y).extend (𝓡∂ 1) ⊥ = 0 := by
  norm_num [IccLeftChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

/--
lemma `iccLeftChart_extend_zero` / 引理 `iccLeftChart_extend_zero`

English:
lemma iccLeftChart_extend_zero
  given: {p : Set.Icc x y}
  proof: rfl

中文:
引理 iccLeftChart_extend_zero
  条件: {p : 集合.闭区间 x y}
  证明: rfl
-/
lemma iccLeftChart_extend_zero {p : Set.Icc x y} :
    (IccLeftChart x y).extend (𝓡∂ 1) p 0 = p.val - x := rfl

/--
lemma `IccLeftChart_extend_interior_pos` / 引理 `IccLeftChart_extend_interior_pos`

English:
lemma IccLeftChart_extend_interior_pos
  given: {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y)
  proof: by
  simp_rw [iccLeftChart_extend_zero]
  norm_num [hp.1]

中文:
引理 IccLeftChart_extend_interior_pos
  条件: {p : 集合.闭区间 x y} (hp : x < p.val ∧ p.val < y)
  证明: by
  simp_rw [iccLeftChart_extend_zero]
  norm_num [hp.1]

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0_iff_fintype, Classical, Classical.choice, Module, Module.rank_lt_aleph0, choice, hs.linearIndepOn_extend, hs.span_extend_eq_span, iccLeftChart_extend_zero, linearIndepOn_extend, lt_aleph0_iff_fintype, rank_lt_aleph0, rank_span_set, simp_rw, span_extend_eq_span
-/
lemma IccLeftChart_extend_interior_pos {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    0 < (IccLeftChart x y).extend (𝓡∂ 1) p 0 := by
  simp_rw [iccLeftChart_extend_zero]
  norm_num [hp.1]

/--
lemma `IccLeftChart_extend_bot_mem_frontier` / 引理 `IccLeftChart_extend_bot_mem_frontier`

English:
lemma IccLeftChart_extend_bot_mem_frontier
  proof: by
  rw [IccLeftChart_extend_bot]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

中文:
引理 IccLeftChart_extend_bot_mem_frontier
  证明: by
  rw [IccLeftChart_extend_bot]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

Depends on / 依赖: IccLeftChart_extend_bot, PiLp.zero_apply, frontier_range_modelWithCornersEuclideanHalfSpace, mem_ofPred, zero_apply
-/
lemma IccLeftChart_extend_bot_mem_frontier :
    (IccLeftChart x y).extend (𝓡∂ 1) ⊥ in frontier (range (𝓡∂ 1)) := by
  rw [IccLeftChart_extend_bot]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

/--
Definition of `IccRightChart` / `IccRightChart` 的定义

English:
definition IccRightChart
  signature: (x y : Real) [h : Fact (x < y)]
  body: { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨toLp 2 fun _ => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩
  map_source' := by simp
  map_target' := by
    simp only 

中文:
定义 IccRightChart
  签名: (x y : 实数) [h : Fact (x < y)]
  定义体: { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨toLp 2 fun _ => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩
  map_source' := by simp
  map_target' := by
    simp only 

Depends on / 依赖: z.val
-/
def IccRightChart (x y : Real) [h : Fact (x < y)] :
    OpenPartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨toLp 2 fun _ => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩
  map_source' := by simp
  map_target' := by
    simp only [lt_max_iff, mem_ofPred_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_ofPred_eq, mem_Icc] at hz h'z
    simp only [Fin.isValue, sub_eq_add_neg, neg_add_rev, neg_neg,
      add_neg_cancel_comm_assoc, hz, sup_of_le_left]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    ext i
    dsimp at hz h'z
    have A : x <= y - z 0 := by linarith
    rw [Subsingleton.elim i 0]
    simp only [Fin.isValue, A, sup_of_le_left, sub_sub_cancel]
  open_source :=
    haveI : IsOpen { z : Real | x < z } := isOpen_Ioi
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : Real | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace Real (Fin 1) | z 0 < y - x } :=
      this.preimage (@PiLp.continuous_apply 2 (Fin 1) (fun _ => Real) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

/--
lemma `IccRightChart_apply` / 引理 `IccRightChart_apply`

English:
lemma IccRightChart_apply
  given: (z : Icc x y)
  proof: rfl

中文:
引理 IccRightChart_apply
  条件: (z : 闭区间 x y)
  证明: rfl
-/
lemma IccRightChart_apply (z : Icc x y) :
    IccRightChart x y z = ⟨toLp 2 fun _ => y - z.val, by aesop⟩ :=
  rfl

/--
lemma `IccRightChart_symm_apply` / 引理 `IccRightChart_symm_apply`

English:
lemma IccRightChart_symm_apply
  given: (x y : Real) [h : Fact (x < y)] (z : EuclideanHalfSpace 1)
  proof: rfl

中文:
引理 IccRightChart_symm_apply
  条件: (x y : 实数) [h : Fact (x < y)] (z : EuclideanHalfSpace 1)
  证明: rfl
-/
lemma IccRightChart_symm_apply (x y : Real) [h : Fact (x < y)] (z : EuclideanHalfSpace 1) :
    (IccRightChart x y).symm z =
      ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩ :=
  rfl

/--
lemma `IccRightChart_symm_apply_of_le` / 引理 `IccRightChart_symm_apply_of_le`

English:
lemma IccRightChart_symm_apply_of_le
  given: {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x)
  proof: by
  ext
  simp only [IccRightChart_symm_apply, sup_eq_left]
  linarith

中文:
引理 IccRightChart_symm_apply_of_le
  条件: {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x)
  证明: by
  ext
  simp only [IccRightChart_symm_apply, sup_eq_left]
  linarith

Depends on / 依赖: IccRightChart_symm_apply, sup_eq_left
-/
lemma IccRightChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 <= y - x) :
    (IccRightChart x y).symm z =
      ⟨y - z.val 0, by simp [z.prop, sub_eq_add_neg, add_le_of_le_sub_left hz]⟩ := by
  ext
  simp only [IccRightChart_symm_apply, sup_eq_left]
  linarith

/--
lemma `IccRightChart_extend_top` / 引理 `IccRightChart_extend_top`

English:
lemma IccRightChart_extend_top
  proof: by
  norm_num [IccRightChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

中文:
引理 IccRightChart_extend_top
  证明: by
  norm_num [IccRightChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

Depends on / 依赖: IccRightChart, modelWithCornersEuclideanHalfSpace_zero
-/
lemma IccRightChart_extend_top :
    (IccRightChart x y).extend (𝓡∂ 1) ⊤ = 0 := by
  norm_num [IccRightChart, modelWithCornersEuclideanHalfSpace_zero]
  congr

/--
lemma `IccRightChart_extend_top_mem_frontier` / 引理 `IccRightChart_extend_top_mem_frontier`

English:
lemma IccRightChart_extend_top_mem_frontier
  proof: by
  rw [IccRightChart_extend_top]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

中文:
引理 IccRightChart_extend_top_mem_frontier
  证明: by
  rw [IccRightChart_extend_top]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

Depends on / 依赖: IccRightChart_extend_top, PiLp.zero_apply, frontier_range_modelWithCornersEuclideanHalfSpace, mem_ofPred, zero_apply
-/
lemma IccRightChart_extend_top_mem_frontier :
    (IccRightChart x y).extend (𝓡∂ 1) ⊤ in frontier (range (𝓡∂ 1)) := by
  rw [IccRightChart_extend_top]; rw [frontier_range_modelWithCornersEuclideanHalfSpace]; rw [mem_ofPred]; rw [PiLp.zero_apply]

/--
Instance `instIccChartedSpace` / 实例 `instIccChartedSpace`

English:
instance instIccChartedSpace
  signature: (x y : Real) [h : Fact (x < y)]
  body: {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt]

中文:
实例 instIccChartedSpace
  签名: (x y : 实数) [h : Fact (x < y)]
  定义体: {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt]

Depends on / 依赖: IccLeftChart, IccRightChart
-/
instance instIccChartedSpace (x y : Real) [h : Fact (x < y)] :
    ChartedSpace (EuclideanHalfSpace 1) (Icc x y) where
  atlas := {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : Real) < y <;> simp [h']

@[simp]
/--
lemma `Icc_chartedSpaceChartAt` / 引理 `Icc_chartedSpaceChartAt`

English:
lemma Icc_chartedSpaceChartAt
  given: {z : Set.Icc x y}
  proof: rfl

中文:
引理 Icc_chartedSpaceChartAt
  条件: {z : 集合.闭区间 x y}
  证明: rfl
-/
lemma Icc_chartedSpaceChartAt {z : Set.Icc x y} :
    chartAt _ z = if z.val < y then IccLeftChart x y else IccRightChart x y := rfl

/--
lemma `Icc_chartedSpaceChartAt_of_le_top` / 引理 `Icc_chartedSpaceChartAt_of_le_top`

English:
lemma Icc_chartedSpaceChartAt_of_le_top
  given: {z : Set.Icc x y} (h : z.val < y)
  proof: by
  simp [Icc_chartedSpaceChartAt, h]

中文:
引理 Icc_chartedSpaceChartAt_of_le_top
  条件: {z : 集合.闭区间 x y} (h : z.val < y)
  证明: by
  simp [Icc_chartedSpaceChartAt, h]

Depends on / 依赖: Icc_chartedSpaceChartAt
-/
lemma Icc_chartedSpaceChartAt_of_le_top {z : Set.Icc x y} (h : z.val < y) :
    chartAt _ z = IccLeftChart x y := by
  simp [Icc_chartedSpaceChartAt, h]

/--
lemma `Icc_chartedSpaceChartAt_of_top_le` / 引理 `Icc_chartedSpaceChartAt_of_top_le`

English:
lemma Icc_chartedSpaceChartAt_of_top_le
  given: {z : Set.Icc x y} (h : y <= z.val)
  proof: by
  simp [Icc_chartedSpaceChartAt, reduceIte, not_lt.mpr h]

中文:
引理 Icc_chartedSpaceChartAt_of_top_le
  条件: {z : 集合.闭区间 x y} (h : y <= z.val)
  证明: by
  simp [Icc_chartedSpaceChartAt, reduceIte, not_lt.mpr h]

Depends on / 依赖: Icc_chartedSpaceChartAt, not_lt, not_lt.mpr, reduceIte
-/
lemma Icc_chartedSpaceChartAt_of_top_le {z : Set.Icc x y} (h : y <= z.val) :
    chartAt _ z = IccRightChart x y := by
  simp [Icc_chartedSpaceChartAt, reduceIte, not_lt.mpr h]

/--
lemma `Icc_isBoundaryPoint_bot` / 引理 `Icc_isBoundaryPoint_bot`

English:
lemma Icc_isBoundaryPoint_bot
  statement: (𝓡∂ 1).IsBoundaryPoint (⊥ : Set.Icc x y)
  proof: by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top (by simp [hxy.out])]
  exact IccLeftChart_extend_bot_mem_frontier

中文:
引理 Icc_isBoundaryPoint_bot
  结论: (𝓡∂ 1).IsBoundaryPoint (⊥ : 集合.闭区间 x y)
  证明: by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top (by simp [hxy.out])]
  exact IccLeftChart_extend_bot_mem_frontier

Depends on / 依赖: IccLeftChart_extend_bot_mem_frontier, Icc_chartedSpaceChartAt_of_le_top, ModelWithCorners, ModelWithCorners.isBoundaryPoint_iff, extChartAt, hxy.out, isBoundaryPoint_iff
-/
lemma Icc_isBoundaryPoint_bot : (𝓡∂ 1).IsBoundaryPoint (⊥ : Set.Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top (by simp [hxy.out])]
  exact IccLeftChart_extend_bot_mem_frontier

/--
lemma `Icc_isBoundaryPoint_top` / 引理 `Icc_isBoundaryPoint_top`

English:
lemma Icc_isBoundaryPoint_top
  statement: (𝓡∂ 1).IsBoundaryPoint (⊤ : Set.Icc x y)
  proof: by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_top_le (by simp)]
  exact IccRightChart_extend_top_mem_frontier

中文:
引理 Icc_isBoundaryPoint_top
  结论: (𝓡∂ 1).IsBoundaryPoint (⊤ : 集合.闭区间 x y)
  证明: by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_top_le (by simp)]
  exact IccRightChart_extend_top_mem_frontier

Depends on / 依赖: IccRightChart_extend_top_mem_frontier, Icc_chartedSpaceChartAt_of_top_le, ModelWithCorners, ModelWithCorners.isBoundaryPoint_iff, extChartAt, isBoundaryPoint_iff
-/
lemma Icc_isBoundaryPoint_top : (𝓡∂ 1).IsBoundaryPoint (⊤ : Set.Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_top_le (by simp)]
  exact IccRightChart_extend_top_mem_frontier

/--
lemma `Icc_isInteriorPoint_interior` / 引理 `Icc_isInteriorPoint_interior`

English:
lemma Icc_isInteriorPoint_interior
  given: {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y)
  proof: by
  rw [ModelWithCorners.IsInteriorPoint]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top hp.2]; rw [interior_range_modelWithCornersEuclideanHalfSpace]
  exact IccLeftChart_extend_interior_pos hp

中文:
引理 Icc_is整数eriorPoint_interior
  条件: {p : 集合.闭区间 x y} (hp : x < p.val ∧ p.val < y)
  证明: by
  rw [ModelWithCorners.IsInteriorPoint]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top hp.2]; rw [interior_range_modelWithCornersEuclideanHalfSpace]
  exact IccLeftChart_extend_interior_pos hp

Depends on / 依赖: IccLeftChart_extend_interior_pos, Icc_chartedSpaceChartAt_of_le_top, IsInteriorPoint, ModelWithCorners, ModelWithCorners.IsInteriorPoint, extChartAt, interior_range_modelWithCornersEuclideanHalfSpace
-/
lemma Icc_isInteriorPoint_interior {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    (𝓡∂ 1).IsInteriorPoint p := by
  rw [ModelWithCorners.IsInteriorPoint]; rw [extChartAt]; rw [Icc_chartedSpaceChartAt_of_le_top hp.2]; rw [interior_range_modelWithCornersEuclideanHalfSpace]
  exact IccLeftChart_extend_interior_pos hp

/--
lemma `boundary_Icc` / 引理 `boundary_Icc`

English:
lemma boundary_Icc
  statement: (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤}
  proof: by
  ext p
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2 with (hp | hp | hp)
  · have : p = ⊥ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_bot (mem_insert ⊥ {⊤})
  · have : p = ⊤ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_top (mem_inser

中文:
引理 boundary_Icc
  结论: (𝓡∂ 1).boundary (闭区间 x y) = {⊥, ⊤}
  证明: by
  ext p
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2 with (hp | hp | hp)
  · have : p = ⊥ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_bot (mem_insert ⊥ {⊤})
  · have : p = ⊤ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_top (mem_inser

Depends on / 依赖: Icc_isBoundaryPoint_bot, Icc_isBoundaryPoint_top, Icc_isInteriorPoint_interior, ModelWithCorners, ModelWithCorners.compl_boundary, Set.eq_endpoints_or_mem_Ioo_of_mem_Icc, SetCoe, SetCoe.ext, compl_boundary, eq_endpoints_or_mem_Ioo_of_mem_Icc, iff_of_false, iff_of_true, mem_compl_iff, mem_insert, mem_insert_of_mem
-/
lemma boundary_Icc : (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤} := by
  ext p
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2 with (hp | hp | hp)
  · have : p = ⊥ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_bot (mem_insert ⊥ {⊤})
  · have : p = ⊤ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_top (mem_insert_of_mem ⊥ rfl)
  · apply iff_of_false
    · simpa [← mem_compl_iff, ModelWithCorners.compl_boundary] using!
        Icc_isInteriorPoint_interior hp
    · rintro (rfl | rfl) <;> simp at hp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
lemma `boundary_product` / 引理 `boundary_product`

English:
lemma boundary_product
  given: [I.Boundaryless]
  proof: by
  rw [I.boundary_of_boundaryless_left]; rw [boundary_Icc]

中文:
引理 boundary_product
  条件: [I.无边界]
  证明: by
  rw [I.boundary_of_boundaryless_left]; rw [boundary_Icc]

Depends on / 依赖: I.boundary_of_boundaryless_left, boundary_Icc, boundary_of_boundaryless_left
-/
lemma boundary_product [I.Boundaryless] :
    (I.prod (𝓡∂ 1)).boundary (M × Icc x y) = Set.prod univ {⊥, ⊤} := by
  rw [I.boundary_of_boundaryless_left]; rw [boundary_Icc]

/--
Instance `instIsManifoldIcc` / 实例 `instIsManifoldIcc`

English:
instance instIsManifoldIcc
  signature: (x y : Real) [Fact (x < y)] {n : Nat∞ω}
  body: by
  have M : ContDiff Real n (show EuclideanSpace Real (Fin 1) -> EuclideanSpace Real (Fin 1)
      from fun z => toLp 2 fun i => -z i + (y - x)) :=
PiLp.contDiff_toLp.comp PiLp.contDiff_ofLp.neg.add contDiff_const
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
 

中文:
实例 instIsManifoldIcc
  签名: (x y : 实数) [Fact (x < y)] {n : 自然数∞ω}
  定义体: by
  have M : ContDiff Real n (show EuclideanSpace Real (Fin 1) -> EuclideanSpace Real (Fin 1)
      from fun z => toLp 2 fun i => -z i + (y - x)) :=
PiLp.contDiff_toLp.comp PiLp.contDiff_ofLp.neg.add contDiff_const
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
 

Depends on / 依赖: ContDiff, EuclideanSpace, PiLp.contDiff_ofLp.neg.add, PiLp.contDiff_toLp.comp, contDiff_const, contDiff_ofLp, contDiff_toLp, isManifold_of_contDiffOn
-/
instance instIsManifoldIcc (x y : Real) [Fact (x < y)] {n : Nat∞ω} :
    IsManifold (𝓡∂ 1) n (Icc x y) := by
  have M : ContDiff Real n (show EuclideanSpace Real (Fin 1) -> EuclideanSpace Real (Fin 1)
      from fun z => toLp 2 fun i => -z i + (y - x)) :=
PiLp.contDiff_toLp.comp PiLp.contDiff_ofLp.neg.add contDiff_const
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
  /- We need to check that any composition of two charts gives a `C^∞` function. Each chart can be
  either the left chart or the right chart, leaving 4 possibilities that we handle successively. -/
  rcases he with (rfl | rfl) <;> rcases he' with (rfl | rfl)
  · -- `e = left chart`, `e' = left chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · -- `e = left chart`, `e' = right chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, update_self,
      max_eq_left, hz₀, lt_sub_iff_add_lt, mfld_simps] at hz₁ hz₂
    rw [min_eq_left hz₁.le]; rw [lt_add_iff_pos_left] at hz₂
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, *,
      max_eq_left, min_eq_left hz₁.le, update_self, mfld_simps]
    abel
  · -- `e = right chart`, `e' = left chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨z, hz₀⟩, rfl⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, max_lt_iff,
      update_self, max_eq_left hz₀, mfld_simps] at hz₁ hz₂
    rw [lt_sub_comm] at hz₁
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart,
      update_self, max_eq_left, hz₀, hz₁.le, mfld_simps]
    abel
  · -- `e = right chart`, `e' = right chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1

/-! Register the manifold structure on `Icc 0 1`. These are merely special cases of
`instIccChartedSpace` and `instIsManifoldIcc`. -/

section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : Real) 1)
  body: by infer_instance

中文:
实例 :
  签名: Charted空间 (EuclideanHalfSpace 1) (闭区间 (0 : 实数) 1)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : Real) 1) := by infer_instance

instance {n : Nat∞ω} : IsManifold (𝓡∂ 1) n (Icc (0 : Real) 1) := by infer_instance

end
