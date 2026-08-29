/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The topological dual of a cone and Farkas' lemma

Given a continuous bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`,
we define `ProperCone.dual p C` to be the proper cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone.
See `Mathlib/Geometry/Convex/Cone/Dual.lean` for that case.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. This is developed here.

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
As a corollary, we prove that the double dual of a proper cone is itself.

## Main statements

We prove the following theorems:
* `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`: Farkas lemma.
* `ProperCone.dual_dual_flip`, `ProperCone.dual_flip_dual`: The double dual of a proper cone.

## References

* https://en.wikipedia.org/wiki/Hyperplane_separation_theorem
* https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Set LinearMap Pointwise

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [TopologicalSpace R] [ClosedIciTopology R]
  [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [TopologicalSpace N]
  {p : M ->ₗ[R] N ->ₗ[R] R} {s : Set M}

/--
lemma `isClosed_dual` / 引理 `isClosed_dual`

English:
lemma isClosed_dual
  given: (hp : forall x, Continuous (p x))
  statement: IsClosed (dual p s : Set N)
  proof: by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
exact isClosed_biInter fun x hx => isClosed_Ici.preimage hp _

中文:
引理 isClosed_dual
  条件: (hp : 对任意 x, Continuous (p x))
  结论: IsClosed (dual p s : Set N)
  证明: by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
exact isClosed_biInter fun x hx => isClosed_Ici.preimage hp _

Depends on / 依赖: Submodule, Submodule.coe_iInf, biUnion_of_singleton, coe_iInf, dual_iUnion, dual_singleton, isClosed_Ici, isClosed_Ici.preimage, isClosed_biInter, preimage, s.biUnion_of_singleton, simp_rw
-/
lemma isClosed_dual (hp : forall x, Continuous (p x)) : IsClosed (dual p s : Set N) := by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
exact isClosed_biInter fun x hx => isClosed_Ici.preimage hp _

end PointedCone

namespace ProperCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [ClosedIciTopology R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  {p : M ->ₗ[R] N ->ₗ[R] R} [p.IsContPerfPair] {s t : Set M} {y : N}

variable (p s) in
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: (s : Set M)
  body: PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ => p.continuous_of_isContPerfPair

中文:
定义 dual
  签名: (s : Set M)
  定义体: PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ => p.continuous_of_isContPerfPair

Depends on / 依赖: PointedCone, PointedCone.dual
-/
def dual (s : Set M) : ProperCone R N where
  toSubmodule := PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ => p.continuous_of_isContPerfPair

/--
lemma `mem_dual` / 引理 `mem_dual`

English:
lemma mem_dual
  statement: y in dual p s ↔ forall ⦃x⦄, x in s -> 0 <= p x y
  proof: .rfl

中文:
引理 mem_dual
  结论: y in dual p s ↔ 对任意 ⦃x⦄, x in s -> 0 <= p x y
  证明: .rfl
-/
@[simp] lemma mem_dual : y in dual p s ↔ forall ⦃x⦄, x in s -> 0 <= p x y := .rfl

/--
lemma `dual_empty` / 引理 `dual_empty`

English:
lemma dual_empty
  statement: dual p ∅ = ⊤
  proof: by ext; simp

中文:
引理 dual_empty
  结论: dual p ∅ = ⊤
  证明: by ext; simp
-/
@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
/--
lemma `dual_zero` / 引理 `dual_zero`

English:
lemma dual_zero
  statement: dual p 0 = ⊤
  proof: by ext; simp

中文:
引理 dual_zero
  结论: dual p 0 = ⊤
  证明: by ext; simp
-/
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp

/--
lemma `dual_univ` / 引理 `dual_univ`

English:
lemma dual_univ
  given: [IsTopologicalRing R] [T1Space N]
  statement: dual p univ = ⊥
  proof: by
  refine le_antisymm (fun y hy => (_root_.map_eq_zero_iff _ p.flip.toContPerfPair.injective).1 ?_)
    (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)

中文:
引理 dual_univ
  条件: [IsTopologicalRing R] [T1Space N]
  结论: dual p univ = ⊥
  证明: by
  refine le_antisymm (fun y hy => (_root_.map_eq_zero_iff _ p.flip.toContPerfPair.injective).1 ?_)
    (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)
-/
@[simp] lemma dual_univ [IsTopologicalRing R] [T1Space N] : dual p univ = ⊥ := by
  refine le_antisymm (fun y hy => (_root_.map_eq_zero_iff _ p.flip.toContPerfPair.injective).1 ?_)
    (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)

/--
lemma `dual_le_dual` / 引理 `dual_le_dual`

English:
lemma dual_le_dual
  given: (h : t subseteq s)
  statement: dual p s <= dual p t
  proof: fun _y hy _x hx => hy (h hx)

中文:
引理 dual_le_dual
  条件: (h : t subseteq s)
  结论: dual p s <= dual p t
  证明: fun _y hy _x hx => hy (h hx)
-/
@[gcongr] lemma dual_le_dual (h : t subseteq s) : dual p s <= dual p t := fun _y hy _x hx => hy (h hx)

/--
lemma `dual_singleton` / 引理 `dual_singleton`

English:
lemma dual_singleton
  given: [IsTopologicalRing R] [OrderClosedTopology R] (x : M)
  proof: by ext; simp

中文:
引理 dual_singleton
  条件: [IsTopologicalRing R] [OrderClosedTopology R] (x : M)
  证明: by ext; simp
-/
lemma dual_singleton [IsTopologicalRing R] [OrderClosedTopology R] (x : M) :
    dual p {x} = (positive R R).comap (p.toContPerfPair x) := by ext; simp

/--
lemma `dual_union` / 引理 `dual_union`

English:
lemma dual_union
  given: (s t : Set M)
  statement: dual p (s union t) = dual p s ⊓ dual p t
  proof: by aesop

中文:
引理 dual_union
  条件: (s t : Set M)
  结论: dual p (s union t) = dual p s ⊓ dual p t
  证明: by aesop
-/
lemma dual_union (s t : Set M) : dual p (s union t) = dual p s ⊓ dual p t := by aesop

/--
lemma `dual_insert` / 引理 `dual_insert`

English:
lemma dual_insert
  given: (x : M) (s : Set M)
  statement: dual p (insert x s) = dual p {x} ⊓ dual p s
  proof: by
  rw [insert_eq]; rw [dual_union]

中文:
引理 dual_insert
  条件: (x : M) (s : Set M)
  结论: dual p (insert x s) = dual p {x} ⊓ dual p s
  证明: by
  rw [insert_eq]; rw [dual_union]

Depends on / 依赖: dual_union, insert_eq
-/
lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq]; rw [dual_union]

/--
lemma `dual_iUnion` / 引理 `dual_iUnion`

English:
lemma dual_iUnion
  given: {ι : Sort*} (f : ι -> Set M)
  statement: dual p (⋃ i, f i) = ⨅ i, dual p (f i)
  proof: by
  ext; simp [forall_comm (α := M)]

中文:
引理 dual_iUnion
  条件: {ι : Sort*} (f : ι -> Set M)
  结论: dual p (⋃ i, f i) = ⨅ i, dual p (f i)
  证明: by
  ext; simp [forall_comm (α := M)]

Depends on / 依赖: forall_comm
-/
lemma dual_iUnion {ι : Sort*} (f : ι -> Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_comm (α := M)]

/--
lemma `dual_sUnion` / 引理 `dual_sUnion`

English:
lemma dual_sUnion
  given: (S : Set (Set M))
  statement: dual p (⋃₀ S) = sInf (dual p '' S)
  proof: by
  ext; simp [forall_comm (α := M)]

中文:
引理 dual_sUnion
  条件: (S : Set (Set M))
  结论: dual p (⋃₀ S) = sInf (dual p '' S)
  证明: by
  ext; simp [forall_comm (α := M)]

Depends on / 依赖: forall_comm
-/
lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_comm (α := M)]

/--
lemma `subset_dual_dual` / 引理 `subset_dual_dual`

English:
lemma subset_dual_dual
  statement: s subseteq dual p.flip (dual p s)
  proof: fun _x hx _y hy => hy hx

中文:
引理 subset_dual_dual
  结论: s subseteq dual p.flip (dual p s)
  证明: fun _x hx _y hy => hy hx
-/
lemma subset_dual_dual : s subseteq dual p.flip (dual p s) := fun _x hx _y hy => hy hx

end ProperCone

namespace ProperCone
variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F]
  [Module Real E] [ContinuousSMul Real E] [LocallyConvexSpace Real E]
  [Module Real F]
  {K : Set E} {x₀ : E}

/--
theorem `hyperplane_separation` / 定理 `hyperplane_separation`

English:
theorem hyperplane_separation
  statement: (C : ProperCone Real E) (hKconv : Convex Real K) (hKcomp : IsCompact K)
  proof: by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
refine ⟨f, fun x hx => ?_, fun x hx => (hu x hx).trans_l

中文:
定理 hyperplane_separation
  结论: (C : 命题erCone 实数 E) (hKconv : Convex 实数 K) (hKcomp : IsCompact K)
  证明: by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
refine ⟨f, fun x hx => ?_, fun x hx => (hu x hx).trans_l

Depends on / 依赖: C.convex, C.isClosed, C.smul_mem, C.zero_mem, K.eq_empty_or_nonempty, convex, eq_empty_or_nonempty, geometric_hahn_banach_compact_closed, hKcomp, hKconv, huv.le.trans, inv_neg, isClosed, le_of_lt, mul_pos_of_neg_of_neg, smul_mem, trans_le, zero_mem
-/
theorem hyperplane_separation (C : ProperCone Real E) (hKconv : Convex Real K) (hKcomp : IsCompact K)
    (hKC : Disjoint K C) : exists f : StrongDual Real E, (forall x in C, 0 <= f x) ∧ forall x in K, f x < 0 := by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
refine ⟨f, fun x hx => ?_, fun x hx => (hu x hx).trans_le huv.le.trans hv₀.le⟩
  by_contra! hx₀
  simpa [hx₀.ne] using hv ((v * (f x)⁻¹) • x)
    (C.smul_mem hx <| le_of_lt <| mul_pos_of_neg_of_neg hv₀ <| inv_neg''.2 hx₀)

/--
theorem `hyperplane_separation_point` / 定理 `hyperplane_separation_point`

English:
theorem hyperplane_separation_point
  given: (C : ProperCone Real E) (hx₀ : x₀ ∉ C)
  proof: by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

中文:
定理 hyperplane_separation_point
  条件: (C : 命题erCone 实数 E) (hx₀ : x₀ ∉ C)
  证明: by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

Depends on / 依赖: C.hyperplane_separation, convex_singleton, hyperplane_separation
-/
theorem hyperplane_separation_point (C : ProperCone Real E) (hx₀ : x₀ ∉ C) :
    exists f : StrongDual Real E, (forall x in C, 0 <= f x) ∧ f x₀ < 0 := by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

/--
theorem `dual_flip_dual` / 定理 `dual_flip_dual`

English:
theorem dual_flip_dual
  given: (p : E ->ₗ[Real] F ->ₗ[Real] Real) [p.IsContPerfPair] (C : ProperCone Real E)
  proof: by
  refine le_antisymm (fun x => ?_) subset_dual_dual
  simp only [mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.toContPerfPair.surjective.exists] using C.hyperplane_separation_point

中文:
定理 dual_flip_dual
  条件: (p : E ->ₗ[实数] F ->ₗ[实数] 实数) [p.IsContPerfPair] (C : 命题erCone 实数 E)
  证明: by
  refine le_antisymm (fun x => ?_) subset_dual_dual
  simp only [mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.toContPerfPair.surjective.exists] using C.hyperplane_separation_point
-/
@[simp] theorem dual_flip_dual (p : E ->ₗ[Real] F ->ₗ[Real] Real) [p.IsContPerfPair] (C : ProperCone Real E) :
    dual p.flip (dual p (C : Set E)) = C := by
  refine le_antisymm (fun x => ?_) subset_dual_dual
  simp only [mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.toContPerfPair.surjective.exists] using C.hyperplane_separation_point

/--
theorem `dual_dual_flip` / 定理 `dual_dual_flip`

English:
theorem dual_dual_flip
  given: (p : F ->ₗ[Real] E ->ₗ[Real] Real) [p.IsContPerfPair] (C : ProperCone Real E)
  proof: C.dual_flip_dual p.flip

中文:
定理 dual_dual_flip
  条件: (p : F ->ₗ[实数] E ->ₗ[实数] 实数) [p.IsContPerfPair] (C : 命题erCone 实数 E)
  证明: C.dual_flip_dual p.flip
-/
@[simp] theorem dual_dual_flip (p : F ->ₗ[Real] E ->ₗ[Real] Real) [p.IsContPerfPair] (C : ProperCone Real E) :
    dual p (dual p.flip (C : Set E)) = C := C.dual_flip_dual p.flip

end ProperCone
