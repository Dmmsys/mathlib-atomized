/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner dual cone of a set

We define the inner dual cone of a set `s` in an inner product space to be the proper cone
consisting of all points `y` such that `0 ≤ ⟪x, y⟫` for all `x ∈ s`.

## Main statements

We prove the following theorems:
* `ProperCone.innerDual_innerDual`: The double inner dual of a proper convex cone is itself.
* `ProperCone.hyperplane_separation'`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `C` in a complete, real inner product space `E`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).

## Implementation notes

We do not provide `ConvexCone`- nor `PointedCone`-valued versions of `ProperCone.innerDual` since
the inner dual cone of any set is always closed and contains `0`, i.e. is a proper cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < ⟪x, y⟫}` is a candidate to the name
`ConvexCone.innerDual`.
-/

@[expose] public section

open Set LinearMap Pointwise
open scoped RealInnerProductSpace

variable {R E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
  {s t : Set E} {x x₀ y : E}

open Function

namespace ProperCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
@[simps! toSubmodule]
/--
Definition of `innerDual` / `innerDual` 的定义

English:
definition innerDual
  signature: (s : Set E)
  body: .dual (innerₗ E) s

中文:
定义 innerDual
  签名: (s : 集合 E)
  定义体: .dual (innerₗ E) s
-/
noncomputable def innerDual (s : Set E) : ProperCone Real E := .dual (innerₗ E) s

/--
lemma `mem_innerDual` / 引理 `mem_innerDual`

English:
lemma mem_innerDual
  statement: y in innerDual s ↔ forall ⦃x⦄, x in s -> 0 <= ⟪x, y⟫
  proof: .rfl

中文:
引理 mem_innerDual
  结论: y in innerDual s ↔ 对任意 ⦃x⦄, x in s -> 0 <= ⟪x, y⟫
  证明: .rfl
-/
@[simp] lemma mem_innerDual : y in innerDual s ↔ forall ⦃x⦄, x in s -> 0 <= ⟪x, y⟫ := .rfl

/--
lemma `innerDual_empty` / 引理 `innerDual_empty`

English:
lemma innerDual_empty
  statement: innerDual (∅ : Set E) = ⊤
  proof: by ext; simp

中文:
引理 innerDual_empty
  结论: innerDual (∅ : 集合 E) = ⊤
  证明: by ext; simp
-/
@[simp] lemma innerDual_empty : innerDual (∅ : Set E) = ⊤ := by ext; simp

/--
lemma `innerDual_zero` / 引理 `innerDual_zero`

English:
lemma innerDual_zero
  statement: innerDual (0 : Set E) = ⊤
  proof: by ext; simp

中文:
引理 innerDual_zero
  结论: innerDual (0 : 集合 E) = ⊤
  证明: by ext; simp
-/
@[simp] lemma innerDual_zero : innerDual (0 : Set E) = ⊤ := by ext; simp

/-- Dual cone of the total space is the convex cone `{0}`. -/
@[simp]
/--
lemma `innerDual_univ` / 引理 `innerDual_univ`

English:
lemma innerDual_univ
  statement: innerDual (univ : Set E) = ⊥
  proof: le_antisymm (fun x hx => by simpa using hx (mem_univ (-x))) (by simp)

中文:
引理 innerDual_univ
  结论: innerDual (univ : 集合 E) = ⊥
  证明: le_antisymm (fun x hx => by simpa using hx (mem_univ (-x))) (by simp)

Depends on / 依赖: le_antisymm, mem_univ
-/
lemma innerDual_univ : innerDual (univ : Set E) = ⊥ :=
  le_antisymm (fun x hx => by simpa using hx (mem_univ (-x))) (by simp)

/--
lemma `innerDual_le_innerDual` / 引理 `innerDual_le_innerDual`

English:
lemma innerDual_le_innerDual
  given: (h : t subseteq s)
  statement: innerDual s <= innerDual t
  proof: fun _y hy _x hx => hy (h hx)

中文:
引理 innerDual_le_innerDual
  条件: (h : t subseteq s)
  结论: innerDual s <= innerDual t
  证明: fun _y hy _x hx => hy (h hx)
-/
@[gcongr] lemma innerDual_le_innerDual (h : t subseteq s) : innerDual s <= innerDual t :=
  fun _y hy _x hx => hy (h hx)

/--
lemma `innerDual_singleton` / 引理 `innerDual_singleton`

English:
lemma innerDual_singleton
  given: (x : E)
  proof: by ext; simp

中文:
引理 innerDual_singleton
  条件: (x : E)
  证明: by ext; simp
-/
lemma innerDual_singleton (x : E) :
    innerDual ({x} : Set E) = (positive Real Real).comap (innerSL Real x) := by ext; simp

/--
lemma `innerDual_union` / 引理 `innerDual_union`

English:
lemma innerDual_union
  given: (s t : Set E)
  statement: innerDual (s union t) = innerDual s ⊓ innerDual t
  proof: le_antisymm (le_inf (fun _ hx _ hy => hx <| .inl hy) fun _ hx _ hy => hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h => hx.1 h) (fun h => hx.2 h)

中文:
引理 innerDual_union
  条件: (s t : 集合 E)
  结论: innerDual (s union t) = innerDual s ⊓ innerDual t
  证明: le_antisymm (le_inf (fun _ hx _ hy => hx <| .inl hy) fun _ hx _ hy => hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h => hx.1 h) (fun h => hx.2 h)

Depends on / 依赖: Or.rec, le_antisymm, le_inf
-/
lemma innerDual_union (s t : Set E) : innerDual (s union t) = innerDual s ⊓ innerDual t :=
  le_antisymm (le_inf (fun _ hx _ hy => hx <| .inl hy) fun _ hx _ hy => hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h => hx.1 h) (fun h => hx.2 h)

/--
lemma `innerDual_insert` / 引理 `innerDual_insert`

English:
lemma innerDual_insert
  given: (x : E) (s : Set E)
  proof: by
  rw [insert_eq]; rw [innerDual_union]

中文:
引理 innerDual_insert
  条件: (x : E) (s : 集合 E)
  证明: by
  rw [insert_eq]; rw [innerDual_union]

Depends on / 依赖: innerDual_union, insert_eq
-/
lemma innerDual_insert (x : E) (s : Set E) :
    innerDual (insert x s) = innerDual {x} ⊓ innerDual s := by
  rw [insert_eq]; rw [innerDual_union]

/--
lemma `innerDual_iUnion` / 引理 `innerDual_iUnion`

English:
lemma innerDual_iUnion
  given: {ι : Sort*} (f : ι -> Set E)
  proof: by
  ext; simp [forall_comm (α := E)]

中文:
引理 innerDual_iUnion
  条件: {ι : 类型层*} (f : ι -> 集合 E)
  证明: by
  ext; simp [forall_comm (α := E)]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toInnerProductSpaceable_ofReal, forall_comm, toInnerProductSpaceable_ofReal
-/
lemma innerDual_iUnion {ι : Sort*} (f : ι -> Set E) :
    innerDual (⋃ i, f i) = ⨅ i, innerDual (f i) := by
  ext; simp [forall_comm (α := E)]

/--
lemma `innerDual_sUnion` / 引理 `innerDual_sUnion`

English:
lemma innerDual_sUnion
  given: (S : Set (Set E))
  statement: innerDual (⋃₀ S) = sInf (innerDual '' S)
  proof: by
  ext; simp [forall_comm (α := E)]

中文:
引理 innerDual_sUnion
  条件: (S : 集合 (集合 E))
  结论: innerDual (⋃₀ S) = sInf (innerDual '' S)
  证明: by
  ext; simp [forall_comm (α := E)]

Depends on / 依赖: forall_comm
-/
lemma innerDual_sUnion (S : Set (Set E)) : innerDual (⋃₀ S) = sInf (innerDual '' S) := by
  ext; simp [forall_comm (α := E)]

/-! ### Farkas' lemma and double dual of a cone in a Hilbert space -/

/--
theorem `hyperplane_separation'` / 定理 `hyperplane_separation'`

English:
theorem hyperplane_separation'
  given: (C : ProperCone Real E) (hx₀ : x₀ ∉ C)
  proof: by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  refine ⟨(InnerProductSpace.toDual Real E).symm f, ?_⟩
  simpa [← real_inner_comm _ ((InnerProductSpace.toDual Real E).symm f), *]

@[deprecated (since := "2026-03-23")] alias
  _root_.ConvexCone.hyperplane_separation_of_nonempty_of_isCl

中文:
定理 hyperplane_separation'
  条件: (C : ProperCone 实数 E) (hx₀ : x₀ ∉ C)
  证明: by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  refine ⟨(InnerProductSpace.toDual Real E).symm f, ?_⟩
  simpa [← real_inner_comm _ ((InnerProductSpace.toDual Real E).symm f), *]

@[deprecated (since := "2026-03-23")] alias
  _root_.ConvexCone.hyperplane_separation_of_nonempty_of_isCl

Depends on / 依赖: C.hyperplane_separation_point, InnerProductSpace, InnerProductSpace.toDual, hyperplane_separation_point, real_inner_comm, toDual
-/
theorem hyperplane_separation' (C : ProperCone Real E) (hx₀ : x₀ ∉ C) :
    exists y, (forall x in C, 0 <= ⟪x, y⟫) ∧ ⟪x₀, y⟫ < 0 := by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  refine ⟨(InnerProductSpace.toDual Real E).symm f, ?_⟩
  simpa [← real_inner_comm _ ((InnerProductSpace.toDual Real E).symm f), *]

@[deprecated (since := "2026-03-23")] alias
  _root_.ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem :=
  hyperplane_separation'

/--
theorem `innerDual_innerDual` / 定理 `innerDual_innerDual`

English:
theorem innerDual_innerDual
  given: (C : ProperCone Real E)
  proof: by
  simpa using! C.dual_flip_dual (innerₗ E)

中文:
定理 innerDual_innerDual
  条件: (C : ProperCone 实数 E)
  证明: by
  simpa using! C.dual_flip_dual (innerₗ E)
-/
@[simp] theorem innerDual_innerDual (C : ProperCone Real E) :
    innerDual (innerDual (C : Set E)) = C := by
  simpa using! C.dual_flip_dual (innerₗ E)

open scoped InnerProductSpace

/--
theorem `relative_hyperplane_separation` / 定理 `relative_hyperplane_separation`

English:
theorem relative_hyperplane_separation
  given: {C : ProperCone Real E} {f : E ->L[Real] F} {b : F}
  proof: by
    -- suppose `b ∈ C.map f`
    simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
      AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
      ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_restrictScalars', ClosedS

中文:
定理 relative_hyperplane_separation
  条件: {C : ProperCone 实数 E} {f : E ->L[实数] F} {b : F}
  证明: by
    -- suppose `b ∈ C.map f`
    simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
      AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
      ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_restrictScalars', ClosedS
-/
theorem relative_hyperplane_separation {C : ProperCone Real E} {f : E ->L[Real] F} {b : F} :
    b in C.map f ↔ forall y : F, f.adjoint y in innerDual C -> 0 <= ⟪b, y⟫_Real where
  mp := by
    -- suppose `b ∈ C.map f`
    simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
      AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
      ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_restrictScalars', ClosedSubmodule.coe_toSubmodule,
      ClosedSubmodule.mem_mk, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, Classical.skolem, forall_and,
      mem_innerDual, ContinuousLinearMap.adjoint_inner_right, forall_exists_index, and_imp]
          -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
    rintro x seq hmem hx htends y hinner
    obtain rfl : f ∘ seq = x := funext hx
    have h n : 0 <= ⟪f (seq n), y⟫_Real := by simpa [real_inner_comm] using hinner (hmem n)
    exact ge_of_tendsto' ((continuous_id.inner continuous_const).seqContinuous htends) h
  mpr h := by
    -- By contradiction, suppose `b ∉ C.map f`.
    contrapose! h
    -- as `b ∉ C.map f`, there is a hyperplane `y` separating `b` from `C.map f`
    obtain ⟨y, hxy, hyb⟩ := (C.map f).hyperplane_separation' h
    -- the rest of the proof is a straightforward algebraic manipulation
    refine ⟨y, fun x hx => ?_, hyb⟩
    simpa [ContinuousLinearMap.adjoint_inner_right]
      using hxy (f x) (subset_closure <| mem_image_of_mem _ hx)

/--
theorem `hyperplane_separation_of_notMem` / 定理 `hyperplane_separation_of_notMem`

English:
theorem hyperplane_separation_of_notMem
  statement: (K : ProperCone Real E) {f : E ->L[Real] F} {b : F}
  proof: by
  contrapose! disj; rwa [K.relative_hyperplane_separation]

中文:
定理 hyperplane_separation_of_notMem
  结论: (K : ProperCone 实数 E) {f : E ->L[实数] F} {b : F}
  证明: by
  contrapose! disj; rwa [K.relative_hyperplane_separation]

Depends on / 依赖: K.relative_hyperplane_separation, contrapose, relative_hyperplane_separation
-/
theorem hyperplane_separation_of_notMem (K : ProperCone Real E) {f : E ->L[Real] F} {b : F}
    (disj : b ∉ K.map f) :
    exists y : F, ContinuousLinearMap.adjoint f y in innerDual K ∧ ⟪b, y⟫_Real < 0 := by
  contrapose! disj; rwa [K.relative_hyperplane_separation]

end ProperCone
