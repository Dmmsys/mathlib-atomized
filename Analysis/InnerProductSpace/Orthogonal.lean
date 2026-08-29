/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
We make duplicates for `Submodule` and `ClosedSubmodule`.
Some of the more subtle results about the orthogonal complement are delayed to
`Mathlib/Analysis/InnerProductSpace/Projection/`.

See also `BilinForm.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `Submodule.IsOrtho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`Bot`).
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Submodule

variable (K : Submodule 𝕜 E)

/--
Definition of `orthogonal` / `orthogonal` 的定义

English:
definition orthogonal
  signature: : Submodule 𝕜 E where
  body: { v | forall u in K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

中文:
定义 orthogonal
  签名: : Submodule 𝕜 E where
  定义体: { v | forall u in K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K
-/
def orthogonal : Submodule 𝕜 E where
  carrier := { v | forall u in K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

/--
theorem `mem_orthogonal` / 定理 `mem_orthogonal`

English:
theorem mem_orthogonal
  given: (v : E)
  statement: v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0
  proof: Iff.rfl

中文:
定理 mem_orthogonal
  条件: (v : E)
  结论: v in Kᗮ ↔ 对任意 u in K, ⟪u, v⟫ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0 :=
  Iff.rfl

/--
theorem `mem_orthogonal'` / 定理 `mem_orthogonal'`

English:
theorem mem_orthogonal'
  given: (v : E)
  statement: v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0
  proof: by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

中文:
定理 mem_orthogonal'
  条件: (v : E)
  结论: v in Kᗮ ↔ 对任意 u in K, ⟪v, u⟫ = 0
  证明: by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

Depends on / 依赖: inner_eq_zero_symm, mem_orthogonal, simp_rw
-/
theorem mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

variable {K}

/--
theorem `inner_right_of_mem_orthogonal` / 定理 `inner_right_of_mem_orthogonal`

English:
theorem inner_right_of_mem_orthogonal
  given: {u v : E} (hu : u in K) (hv : v in Kᗮ)
  statement: ⟪u, v⟫ = 0
  proof: (K.mem_orthogonal v).1 hv u hu

中文:
定理 inner_right_of_mem_orthogonal
  条件: {u v : E} (hu : u in K) (hv : v in Kᗮ)
  结论: ⟪u, v⟫ = 0
  证明: (K.mem_orthogonal v).1 hv u hu

Depends on / 依赖: K.mem_orthogonal, mem_orthogonal
-/
theorem inner_right_of_mem_orthogonal {u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu

/--
theorem `inner_left_of_mem_orthogonal` / 定理 `inner_left_of_mem_orthogonal`

English:
theorem inner_left_of_mem_orthogonal
  given: {u v : E} (hu : u in K) (hv : v in Kᗮ)
  statement: ⟪v, u⟫ = 0
  proof: by
  rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

中文:
定理 inner_left_of_mem_orthogonal
  条件: {u v : E} (hu : u in K) (hv : v in Kᗮ)
  结论: ⟪v, u⟫ = 0
  证明: by
  rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

Depends on / 依赖: inner_eq_zero_symm, inner_right_of_mem_orthogonal
-/
theorem inner_left_of_mem_orthogonal {u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

/--
theorem `mem_orthogonal_singleton_iff_inner_right` / 定理 `mem_orthogonal_singleton_iff_inner_right`

English:
theorem mem_orthogonal_singleton_iff_inner_right
  given: {u v : E}
  statement: v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
  proof: by
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), ?_⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]

中文:
定理 mem_orthogonal_singleton_iff_inner_right
  条件: {u v : E}
  结论: v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
  证明: by
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), ?_⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]

Depends on / 依赖: inner_right_of_mem_orthogonal, inner_smul_left, mem_span_singleton, mem_span_singleton_self
-/
theorem mem_orthogonal_singleton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 := by
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), ?_⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]

/--
theorem `mem_orthogonal_singleton_iff_inner_left` / 定理 `mem_orthogonal_singleton_iff_inner_left`

English:
theorem mem_orthogonal_singleton_iff_inner_left
  given: {u v : E}
  statement: v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
  proof: by
  rw [mem_orthogonal_singleton_iff_inner_right]; rw [inner_eq_zero_symm]

中文:
定理 mem_orthogonal_singleton_iff_inner_left
  条件: {u v : E}
  结论: v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
  证明: by
  rw [mem_orthogonal_singleton_iff_inner_right]; rw [inner_eq_zero_symm]

Depends on / 依赖: inner_eq_zero_symm, mem_orthogonal_singleton_iff_inner_right
-/
theorem mem_orthogonal_singleton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 := by
  rw [mem_orthogonal_singleton_iff_inner_right]; rw [inner_eq_zero_symm]

/--
theorem `sub_mem_orthogonal_of_inner_left` / 定理 `sub_mem_orthogonal_of_inner_left`

English:
theorem sub_mem_orthogonal_of_inner_left
  given: {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫)
  statement: x - y in Kᗮ
  proof: by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

中文:
定理 sub_mem_orthogonal_of_inner_left
  条件: {x y : E} (h : 对任意 v : K, ⟪x, v⟫ = ⟪y, v⟫)
  结论: x - y in Kᗮ
  证明: by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

Depends on / 依赖: inner_sub_left, mem_orthogonal, sub_eq_zero
-/
theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y in Kᗮ := by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

/--
theorem `sub_mem_orthogonal_of_inner_right` / 定理 `sub_mem_orthogonal_of_inner_right`

English:
theorem sub_mem_orthogonal_of_inner_right
  given: {x y : E} (h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫)
  proof: by
  intro u hu
  rw [inner_sub_right]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

中文:
定理 sub_mem_orthogonal_of_inner_right
  条件: {x y : E} (h : 对任意 v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫)
  证明: by
  intro u hu
  rw [inner_sub_right]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

Depends on / 依赖: inner_sub_right, sub_eq_zero
-/
theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y in Kᗮ := by
  intro u hu
  rw [inner_sub_right]; rw [sub_eq_zero]
  exact h ⟨u, hu⟩

variable (K)

/--
theorem `inf_orthogonal_eq_bot` / 定理 `inf_orthogonal_eq_bot`

English:
theorem inf_orthogonal_eq_bot
  statement: K ⊓ Kᗮ = ⊥
  proof: by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

中文:
定理 inf_orthogonal_eq_bot
  结论: K ⊓ Kᗮ = ⊥
  证明: by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

Depends on / 依赖: eq_bot_iff, inner_self_eq_zero, mem_inf
-/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

/--
theorem `orthogonal_disjoint` / 定理 `orthogonal_disjoint`

English:
theorem orthogonal_disjoint
  statement: Disjoint K Kᗮ
  proof: by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

中文:
定理 orthogonal_disjoint
  结论: Disjoint K Kᗮ
  证明: by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

Depends on / 依赖: K.inf_orthogonal_eq_bot, disjoint_iff, inf_orthogonal_eq_bot
-/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/--
theorem `orthogonal_eq_inter` / 定理 `orthogonal_eq_inter`

English:
theorem orthogonal_eq_inter
  statement: Kᗮ = ⨅ v : K, (innerSL 𝕜 (v : E)).ker
  proof: by
  ext
  simpa using mem_orthogonal _ _

中文:
定理 orthogonal_eq_inter
  结论: Kᗮ = ⨅ v : K, (innerSL 𝕜 (v : E)).ker
  证明: by
  ext
  simpa using mem_orthogonal _ _

Depends on / 依赖: mem_orthogonal
-/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, (innerSL 𝕜 (v : E)).ker := by
  ext
  simpa using mem_orthogonal _ _

/--
theorem `isClosed_orthogonal` / 定理 `isClosed_orthogonal`

English:
theorem isClosed_orthogonal
  statement: IsClosed (Kᗮ : Set E)
  proof: by
  rw [orthogonal_eq_inter K]
convert! isClosed_iInter fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  simp

中文:
定理 isClosed_orthogonal
  结论: IsClosed (Kᗮ : Set E)
  证明: by
  rw [orthogonal_eq_inter K]
convert! isClosed_iInter fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isClosed_ker, convert, innerSL, isClosed_iInter, isClosed_ker, orthogonal_eq_inter
-/
theorem isClosed_orthogonal : IsClosed (Kᗮ : Set E) := by
  rw [orthogonal_eq_inter K]
convert! isClosed_iInter fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  simp

/--
Instance `instOrthogonalCompleteSpace` / 实例 `instOrthogonalCompleteSpace`

English:
instance instOrthogonalCompleteSpace
  signature: [CompleteSpace E]
  body: K.isClosed_orthogonal.completeSpace_coe

中文:
实例 instOrthogonalCompleteSpace
  签名: [CompleteSpace E]
  定义体: K.isClosed_orthogonal.completeSpace_coe

Depends on / 依赖: K.isClosed_orthogonal.completeSpace_coe, completeSpace_coe, isClosed_orthogonal
-/
instance instOrthogonalCompleteSpace [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe

/--
lemma `map_orthogonal` / 引理 `map_orthogonal`

English:
lemma map_orthogonal
  given: (f : E ->ₗᵢ[𝕜] F)
  proof: by
  simp only [Submodule.ext_iff, mem_map, mem_orthogonal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_inf, mem_map, LinearMap.mem_range,
    LinearIsometry.coe_toLinearMap]
  grind [LinearIsometry.inner_map_map]

中文:
引理 map_orthogonal
  条件: (f : E ->ₗᵢ[𝕜] F)
  证明: by
  simp only [Submodule.ext_iff, mem_map, mem_orthogonal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_inf, mem_map, LinearMap.mem_range,
    LinearIsometry.coe_toLinearMap]
  grind [LinearIsometry.inner_map_map]

Depends on / 依赖: LinearIsometry, LinearIsometry.coe_toLinearMap, LinearIsometry.inner_map_map, LinearMap, LinearMap.mem_range, Submodule, Submodule.ext_iff, and_imp, coe_toLinearMap, ext_iff, forall_exists_index, inner_map_map, mem_inf, mem_map, mem_orthogonal, mem_range
-/
lemma map_orthogonal (f : E ->ₗᵢ[𝕜] F) :
    Kᗮ.map f.toLinearMap = (K.map f.toLinearMap)ᗮ ⊓ f.range := by
  simp only [Submodule.ext_iff, mem_map, mem_orthogonal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_inf, mem_map, LinearMap.mem_range,
    LinearIsometry.coe_toLinearMap]
  grind [LinearIsometry.inner_map_map]

/--
lemma `map_orthogonal_equiv` / 引理 `map_orthogonal_equiv`

English:
lemma map_orthogonal_equiv
  given: (f : E ≃ₗᵢ[𝕜] F)
  proof: by
  refine (map_orthogonal K f.toLinearIsometry).trans ?_
  have : f.toLinearIsometry.range = ⊤ := f.range
  rw [this]; rw [inf_top_eq]
  rfl

中文:
引理 map_orthogonal_equiv
  条件: (f : E ≃ₗᵢ[𝕜] F)
  证明: by
  refine (map_orthogonal K f.toLinearIsometry).trans ?_
  have : f.toLinearIsometry.range = ⊤ := f.range
  rw [this]; rw [inf_top_eq]
  rfl

Depends on / 依赖: f.range, f.toLinearIsometry, f.toLinearIsometry.range, inf_top_eq, map_orthogonal, toLinearIsometry
-/
lemma map_orthogonal_equiv (f : E ≃ₗᵢ[𝕜] F) :
    Kᗮ.map (f.toLinearEquiv : E ->ₗ[𝕜] F) = (K.map (f.toLinearEquiv : E ->ₗ[𝕜] F))ᗮ := by
  refine (map_orthogonal K f.toLinearIsometry).trans ?_
  have : f.toLinearIsometry.range = ⊤ := f.range
  rw [this]; rw [inf_top_eq]
  rfl

variable (𝕜 E)

/--
theorem `orthogonal_gc` / 定理 `orthogonal_gc`

English:
theorem orthogonal_gc
  proof: fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩

中文:
定理 orthogonal_gc
  证明: fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩
-/
theorem orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal := fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/--
theorem `orthogonal_le` / 定理 `orthogonal_le`

English:
theorem orthogonal_le
  given: {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
  statement: K₂ᗮ <= K₁ᗮ
  proof: (orthogonal_gc 𝕜 E).monotone_l h

中文:
定理 orthogonal_le
  条件: {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
  结论: K₂ᗮ <= K₁ᗮ
  证明: (orthogonal_gc 𝕜 E).monotone_l h

Depends on / 依赖: monotone_l, orthogonal_gc
-/
theorem orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) : K₂ᗮ <= K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h

/--
theorem `orthogonal_orthogonal_monotone` / 定理 `orthogonal_orthogonal_monotone`

English:
theorem orthogonal_orthogonal_monotone
  given: {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
  statement: K₁ᗮᗮ <= K₂ᗮᗮ
  proof: orthogonal_le (orthogonal_le h)

中文:
定理 orthogonal_orthogonal_monotone
  条件: {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
  结论: K₁ᗮᗮ <= K₂ᗮᗮ
  证明: orthogonal_le (orthogonal_le h)

Depends on / 依赖: orthogonal_le
-/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) : K₁ᗮᗮ <= K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)

/--
theorem `le_orthogonal_orthogonal` / 定理 `le_orthogonal_orthogonal`

English:
theorem le_orthogonal_orthogonal
  statement: K <= Kᗮᗮ
  proof: (orthogonal_gc 𝕜 E).le_u_l _

中文:
定理 le_orthogonal_orthogonal
  结论: K <= Kᗮᗮ
  证明: (orthogonal_gc 𝕜 E).le_u_l _

Depends on / 依赖: le_u_l, orthogonal_gc
-/
theorem le_orthogonal_orthogonal : K <= Kᗮᗮ :=
  (orthogonal_gc 𝕜 E).le_u_l _

/--
theorem `inf_orthogonal` / 定理 `inf_orthogonal`

English:
theorem inf_orthogonal
  given: (K₁ K₂ : Submodule 𝕜 E)
  statement: K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_sup.symm

中文:
定理 inf_orthogonal
  条件: (K₁ K₂ : Submodule 𝕜 E)
  结论: K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_sup.symm

Depends on / 依赖: l_sup, l_sup.symm, orthogonal_gc
-/
theorem inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm

/--
theorem `iInf_orthogonal` / 定理 `iInf_orthogonal`

English:
theorem iInf_orthogonal
  given: {ι : Type*} (K : ι -> Submodule 𝕜 E)
  statement: ⨅ i, (K i)ᗮ = (iSup K)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_iSup.symm

中文:
定理 iInf_orthogonal
  条件: {ι : 类型} (K : ι -> Submodule 𝕜 E)
  结论: ⨅ i, (K i)ᗮ = (iSup K)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_iSup.symm

Depends on / 依赖: l_iSup, l_iSup.symm, orthogonal_gc
-/
theorem iInf_orthogonal {ι : Type*} (K : ι -> Submodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm

/--
theorem `sInf_orthogonal` / 定理 `sInf_orthogonal`

English:
theorem sInf_orthogonal
  given: (s : Set <| Submodule 𝕜 E)
  statement: ⨅ K in s, Kᗮ = (sSup s)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]

中文:
定理 sInf_orthogonal
  条件: (s : Set <| Submodule 𝕜 E)
  结论: ⨅ K in s, Kᗮ = (sSup s)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]

Depends on / 依赖: l_sSup, l_sSup.symm, orthogonal_gc
-/
theorem sInf_orthogonal (s : Set <| Submodule 𝕜 E) : ⨅ K in s, Kᗮ = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]
/--
theorem `top_orthogonal_eq_bot` / 定理 `top_orthogonal_eq_bot`

English:
theorem top_orthogonal_eq_bot
  statement: (⊤ : Submodule 𝕜 E)ᗮ = ⊥
  proof: by
  ext x
  rw [mem_bot]; rw [mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top), by
      rintro rfl
      simp⟩

@[simp]

中文:
定理 top_orthogonal_eq_bot
  结论: (⊤ : Submodule 𝕜 E)ᗮ = ⊥
  证明: by
  ext x
  rw [mem_bot]; rw [mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top), by
      rintro rfl
      simp⟩

@[simp]

Depends on / 依赖: inner_self_eq_zero, inner_self_eq_zero.mp, mem_bot, mem_orthogonal, mem_top
-/
theorem top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ := by
  ext x
  rw [mem_bot]; rw [mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top), by
      rintro rfl
      simp⟩

@[simp]
/--
theorem `bot_orthogonal_eq_top` / 定理 `bot_orthogonal_eq_top`

English:
theorem bot_orthogonal_eq_top
  statement: (⊥ : Submodule 𝕜 E)ᗮ = ⊤
  proof: by
  rw [← top_orthogonal_eq_bot]; rw [eq_top_iff]
  exact le_orthogonal_orthogonal ⊤

@[simp]

中文:
定理 bot_orthogonal_eq_top
  结论: (⊥ : Submodule 𝕜 E)ᗮ = ⊤
  证明: by
  rw [← top_orthogonal_eq_bot]; rw [eq_top_iff]
  exact le_orthogonal_orthogonal ⊤

@[simp]

Depends on / 依赖: eq_top_iff, le_orthogonal_orthogonal, top_orthogonal_eq_bot
-/
theorem bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ := by
  rw [← top_orthogonal_eq_bot]; rw [eq_top_iff]
  exact le_orthogonal_orthogonal ⊤

@[simp]
/--
theorem `orthogonal_eq_top_iff` / 定理 `orthogonal_eq_top_iff`

English:
theorem orthogonal_eq_top_iff
  statement: Kᗮ = ⊤ ↔ K = ⊥
  proof: by
  refine
    ⟨?_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

中文:
定理 orthogonal_eq_top_iff
  结论: Kᗮ = ⊤ ↔ K = ⊥
  证明: by
  refine
    ⟨?_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

Depends on / 依赖: K.orthogonal_disjoint.eq_bot, bot_orthogonal_eq_top, eq_bot, inf_comm, orthogonal_disjoint, top_inf_eq
-/
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine
    ⟨?_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

/-- The closure of a submodule has the same orthogonal complement and the submodule itself. -/
@[simp]
/--
lemma `orthogonal_closure` / 引理 `orthogonal_closure`

English:
lemma orthogonal_closure
  given: (K : Submodule 𝕜 E)
  statement: K.topologicalClosureᗮ = Kᗮ
  proof: le_antisymm (orthogonal_le <| le_topologicalClosure _)
    fun x hx y hy => closure_minimal hx (isClosed_eq (by fun_prop) (by fun_prop)) hy

中文:
引理 orthogonal_closure
  条件: (K : Submodule 𝕜 E)
  结论: K.topologicalClosureᗮ = Kᗮ
  证明: le_antisymm (orthogonal_le <| le_topologicalClosure _)
    fun x hx y hy => closure_minimal hx (isClosed_eq (by fun_prop) (by fun_prop)) hy

Depends on / 依赖: closure_minimal, fun_prop, isClosed_eq, le_antisymm, le_topologicalClosure, orthogonal_le
-/
lemma orthogonal_closure (K : Submodule 𝕜 E) : K.topologicalClosureᗮ = Kᗮ :=
  le_antisymm (orthogonal_le <| le_topologicalClosure _)
    fun x hx y hy => closure_minimal hx (isClosed_eq (by fun_prop) (by fun_prop)) hy

/--
lemma `orthogonal_closure'` / 引理 `orthogonal_closure'`

English:
lemma orthogonal_closure'
  given: (K : Submodule 𝕜 E) (x : E)
  proof: by
  simp_rw [← mem_orthogonal, orthogonal_closure]

中文:
引理 orthogonal_closure'
  条件: (K : Submodule 𝕜 E) (x : E)
  证明: by
  simp_rw [← mem_orthogonal, orthogonal_closure]

Depends on / 依赖: mem_orthogonal, orthogonal_closure, simp_rw
-/
lemma orthogonal_closure' (K : Submodule 𝕜 E) (x : E) :
    (forall y in K, ⟪y, x⟫ = 0) ↔ forall y in K.topologicalClosure, ⟪y, x⟫ = 0 := by
  simp_rw [← mem_orthogonal, orthogonal_closure]

/--
theorem `orthogonalFamily_self` / 定理 `orthogonalFamily_self`

English:
theorem orthogonalFamily_self

中文:
定理 orthogonalFamily_self
-/
theorem orthogonalFamily_self :
    OrthogonalFamily 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
  | true, true => absurd rfl
  | true, false => fun _ x y => inner_right_of_mem_orthogonal x.prop y.prop
  | false, true => fun _ x y => inner_left_of_mem_orthogonal y.prop x.prop
  | false, false => absurd rfl

end Submodule

@[simp]
/--
theorem `orthogonalBilin_innerₗ` / 定理 `orthogonalBilin_innerₗ`

English:
theorem orthogonalBilin_innerₗ
  statement: {E} [NormedAddCommGroup E] [InnerProductSpace Real E]
  proof: rfl

中文:
定理 orthogonalBilin_innerₗ
  结论: {E} [NormedAddCommGroup E] [InnerProductSpace 实数 E]
  证明: rfl
-/
theorem orthogonalBilin_innerₗ {E} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (K : Submodule Real E) : K.orthogonalBilin (innerₗ E) = Kᗮ :=
  rfl

/-!
### Orthogonality of submodules

In this section we define `Submodule.IsOrtho U V`, denoted as `U ⟂ V`.

The API roughly matches that of `Disjoint`.
-/


namespace Submodule

/--
Definition of `IsOrtho` / `IsOrtho` 的定义

English:
definition IsOrtho
  signature: (U V : Submodule 𝕜 E)
  body: U <= Vᗮ

@[inherit_doc]
infixl:50 " ⟂ " => Submodule.IsOrtho

中文:
定义 IsOrtho
  签名: (U V : Submodule 𝕜 E)
  定义体: U <= Vᗮ

@[inherit_doc]
infixl:50 " ⟂ " => Submodule.IsOrtho
-/
def IsOrtho (U V : Submodule 𝕜 E) : Prop :=
  U <= Vᗮ

@[inherit_doc]
infixl:50 " ⟂ " => Submodule.IsOrtho

/--
theorem `isOrtho_iff_le` / 定理 `isOrtho_iff_le`

English:
theorem isOrtho_iff_le
  given: {U V : Submodule 𝕜 E}
  statement: U ⟂ V ↔ U <= Vᗮ
  proof: Iff.rfl

@[symm]

中文:
定理 isOrtho_iff_le
  条件: {U V : Submodule 𝕜 E}
  结论: U ⟂ V ↔ U <= Vᗮ
  证明: Iff.rfl

@[symm]

Depends on / 依赖: Iff.rfl
-/
theorem isOrtho_iff_le {U V : Submodule 𝕜 E} : U ⟂ V ↔ U <= Vᗮ :=
  Iff.rfl

@[symm]
/--
theorem `IsOrtho.symm` / 定理 `IsOrtho.symm`

English:
theorem IsOrtho.symm
  given: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  statement: V ⟂ U
  proof: (le_orthogonal_orthogonal _).trans (orthogonal_le h)

中文:
定理 IsOrtho.symm
  条件: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  结论: V ⟂ U
  证明: (le_orthogonal_orthogonal _).trans (orthogonal_le h)

Depends on / 依赖: le_orthogonal_orthogonal, orthogonal_le
-/
theorem IsOrtho.symm {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
  (le_orthogonal_orthogonal _).trans (orthogonal_le h)

/--
theorem `isOrtho_comm` / 定理 `isOrtho_comm`

English:
theorem isOrtho_comm
  given: {U V : Submodule 𝕜 E}
  statement: U ⟂ V ↔ V ⟂ U
  proof: ⟨IsOrtho.symm, IsOrtho.symm⟩

中文:
定理 isOrtho_comm
  条件: {U V : Submodule 𝕜 E}
  结论: U ⟂ V ↔ V ⟂ U
  证明: ⟨IsOrtho.symm, IsOrtho.symm⟩

Depends on / 依赖: IsOrtho, IsOrtho.symm
-/
theorem isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩

/--
Instance `symmetric_isOrtho` / 实例 `symmetric_isOrtho`

English:
instance symmetric_isOrtho
  signature: : Std.Symm IsOrtho (𝕜 := 𝕜) (E := E) where
  body: IsOrtho.symm

中文:
实例 symmetric_isOrtho
  签名: : Std.Symm IsOrtho (𝕜 := 𝕜) (E := E) where
  定义体: IsOrtho.symm
-/
instance symmetric_isOrtho : Std.Symm IsOrtho (𝕜 := 𝕜) (E := E) where
  symm _ _ := IsOrtho.symm

/--
theorem `IsOrtho.inner_eq` / 定理 `IsOrtho.inner_eq`

English:
theorem IsOrtho.inner_eq
  given: {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u in U) (hv : v in V)
  proof: h.symm hv _ hu

中文:
定理 IsOrtho.inner_eq
  条件: {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u in U) (hv : v in V)
  证明: h.symm hv _ hu

Depends on / 依赖: h.symm
-/
theorem IsOrtho.inner_eq {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u in U) (hv : v in V) :
    ⟪u, v⟫ = 0 :=
  h.symm hv _ hu

/--
theorem `isOrtho_iff_inner_eq` / 定理 `isOrtho_iff_inner_eq`

English:
theorem isOrtho_iff_inner_eq
  given: {U V : Submodule 𝕜 E}
  statement: U ⟂ V ↔ forall u in U, forall v in V, ⟪u, v⟫ = 0
  proof: forall₄_congr fun _u _hu _v _hv => inner_eq_zero_symm

中文:
定理 isOrtho_iff_inner_eq
  条件: {U V : Submodule 𝕜 E}
  结论: U ⟂ V ↔ 对任意 u in U, 对任意 v in V, ⟪u, v⟫ = 0
  证明: forall₄_congr fun _u _hu _v _hv => inner_eq_zero_symm

Depends on / 依赖: inner_eq_zero_symm
-/
theorem isOrtho_iff_inner_eq {U V : Submodule 𝕜 E} : U ⟂ V ↔ forall u in U, forall v in V, ⟪u, v⟫ = 0 :=
  forall₄_congr fun _u _hu _v _hv => inner_eq_zero_symm

/-- TODO: generalize `Submodule.map₂` to semilinear maps, so that we can state
`U ⟂ V ↔ Submodule.map₂ (innerₛₗ 𝕜) U V ≤ ⊥`. -/
@[simp]
/--
theorem `isOrtho_bot_left` / 定理 `isOrtho_bot_left`

English:
theorem isOrtho_bot_left
  given: {V : Submodule 𝕜 E}
  statement: ⊥ ⟂ V
  proof: bot_le

@[simp]

中文:
定理 isOrtho_bot_left
  条件: {V : Submodule 𝕜 E}
  结论: ⊥ ⟂ V
  证明: bot_le

@[simp]

Depends on / 依赖: bot_le
-/
theorem isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V :=
  bot_le

@[simp]
/--
theorem `isOrtho_bot_right` / 定理 `isOrtho_bot_right`

English:
theorem isOrtho_bot_right
  given: {U : Submodule 𝕜 E}
  statement: U ⟂ ⊥
  proof: isOrtho_bot_left.symm

中文:
定理 isOrtho_bot_right
  条件: {U : Submodule 𝕜 E}
  结论: U ⟂ ⊥
  证明: isOrtho_bot_left.symm

Depends on / 依赖: isOrtho_bot_left, isOrtho_bot_left.symm
-/
theorem isOrtho_bot_right {U : Submodule 𝕜 E} : U ⟂ ⊥ :=
  isOrtho_bot_left.symm

/--
theorem `IsOrtho.mono_left` / 定理 `IsOrtho.mono_left`

English:
theorem IsOrtho.mono_left
  given: {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ <= U₁) (h : U₁ ⟂ V)
  statement: U₂ ⟂ V
  proof: hU.trans h

中文:
定理 IsOrtho.mono_left
  条件: {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ <= U₁) (h : U₁ ⟂ V)
  结论: U₂ ⟂ V
  证明: hU.trans h

Depends on / 依赖: hU.trans
-/
theorem IsOrtho.mono_left {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ <= U₁) (h : U₁ ⟂ V) : U₂ ⟂ V :=
  hU.trans h

/--
theorem `IsOrtho.mono_right` / 定理 `IsOrtho.mono_right`

English:
theorem IsOrtho.mono_right
  given: {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ <= V₁) (h : U ⟂ V₁)
  statement: U ⟂ V₂
  proof: (h.symm.mono_left hV).symm

中文:
定理 IsOrtho.mono_right
  条件: {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ <= V₁) (h : U ⟂ V₁)
  结论: U ⟂ V₂
  证明: (h.symm.mono_left hV).symm

Depends on / 依赖: h.symm.mono_left, mono_left
-/
theorem IsOrtho.mono_right {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ <= V₁) (h : U ⟂ V₁) : U ⟂ V₂ :=
  (h.symm.mono_left hV).symm

/--
theorem `IsOrtho.mono` / 定理 `IsOrtho.mono`

English:
theorem IsOrtho.mono
  given: {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ <= U₁) (hV : V₂ <= V₁) (h : U₁ ⟂ V₁)
  proof: (h.mono_right hV).mono_left hU

@[simp]

中文:
定理 IsOrtho.mono
  条件: {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ <= U₁) (hV : V₂ <= V₁) (h : U₁ ⟂ V₁)
  证明: (h.mono_right hV).mono_left hU

@[simp]

Depends on / 依赖: h.mono_right, mono_left, mono_right
-/
theorem IsOrtho.mono {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ <= U₁) (hV : V₂ <= V₁) (h : U₁ ⟂ V₁) :
    U₂ ⟂ V₂ :=
  (h.mono_right hV).mono_left hU

@[simp]
/--
theorem `isOrtho_self` / 定理 `isOrtho_self`

English:
theorem isOrtho_self
  given: {U : Submodule 𝕜 E}
  statement: U ⟂ U ↔ U = ⊥
  proof: ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]

中文:
定理 isOrtho_self
  条件: {U : Submodule 𝕜 E}
  结论: U ⟂ U ↔ U = ⊥
  证明: ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr, h.symm, inner_self_eq_zero, inner_self_eq_zero.mp, isOrtho_bot_left
-/
theorem isOrtho_self {U : Submodule 𝕜 E} : U ⟂ U ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
/--
theorem `isOrtho_orthogonal_right` / 定理 `isOrtho_orthogonal_right`

English:
theorem isOrtho_orthogonal_right
  given: (U : Submodule 𝕜 E)
  statement: U ⟂ Uᗮ
  proof: le_orthogonal_orthogonal _

@[simp]

中文:
定理 isOrtho_orthogonal_right
  条件: (U : Submodule 𝕜 E)
  结论: U ⟂ Uᗮ
  证明: le_orthogonal_orthogonal _

@[simp]

Depends on / 依赖: le_orthogonal_orthogonal
-/
theorem isOrtho_orthogonal_right (U : Submodule 𝕜 E) : U ⟂ Uᗮ :=
  le_orthogonal_orthogonal _

@[simp]
/--
theorem `isOrtho_orthogonal_left` / 定理 `isOrtho_orthogonal_left`

English:
theorem isOrtho_orthogonal_left
  given: (U : Submodule 𝕜 E)
  statement: Uᗮ ⟂ U
  proof: (isOrtho_orthogonal_right U).symm

中文:
定理 isOrtho_orthogonal_left
  条件: (U : Submodule 𝕜 E)
  结论: Uᗮ ⟂ U
  证明: (isOrtho_orthogonal_right U).symm

Depends on / 依赖: isOrtho_orthogonal_right
-/
theorem isOrtho_orthogonal_left (U : Submodule 𝕜 E) : Uᗮ ⟂ U :=
  (isOrtho_orthogonal_right U).symm

/--
theorem `IsOrtho.le` / 定理 `IsOrtho.le`

English:
theorem IsOrtho.le
  given: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  statement: U <= Vᗮ
  proof: h

中文:
定理 IsOrtho.le
  条件: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  结论: U <= Vᗮ
  证明: h
-/
theorem IsOrtho.le {U V : Submodule 𝕜 E} (h : U ⟂ V) : U <= Vᗮ :=
  h

/--
theorem `IsOrtho.ge` / 定理 `IsOrtho.ge`

English:
theorem IsOrtho.ge
  given: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  statement: V <= Uᗮ
  proof: h.symm

@[simp]

中文:
定理 IsOrtho.ge
  条件: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  结论: V <= Uᗮ
  证明: h.symm

@[simp]

Depends on / 依赖: h.symm
-/
theorem IsOrtho.ge {U V : Submodule 𝕜 E} (h : U ⟂ V) : V <= Uᗮ :=
  h.symm

@[simp]
/--
theorem `isOrtho_top_right` / 定理 `isOrtho_top_right`

English:
theorem isOrtho_top_right
  given: {U : Submodule 𝕜 E}
  statement: U ⟂ ⊤ ↔ U = ⊥
  proof: ⟨fun h => eq_bot_iff.mpr fun _x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]

中文:
定理 isOrtho_top_right
  条件: {U : Submodule 𝕜 E}
  结论: U ⟂ ⊤ ↔ U = ⊥
  证明: ⟨fun h => eq_bot_iff.mpr fun _x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr, h.symm, inner_self_eq_zero, inner_self_eq_zero.mp, isOrtho_bot_left, mem_top
-/
theorem isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun _x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
/--
theorem `isOrtho_top_left` / 定理 `isOrtho_top_left`

English:
theorem isOrtho_top_left
  given: {V : Submodule 𝕜 E}
  statement: ⊤ ⟂ V ↔ V = ⊥
  proof: isOrtho_comm.trans isOrtho_top_right

中文:
定理 isOrtho_top_left
  条件: {V : Submodule 𝕜 E}
  结论: ⊤ ⟂ V ↔ V = ⊥
  证明: isOrtho_comm.trans isOrtho_top_right

Depends on / 依赖: isOrtho_comm, isOrtho_comm.trans, isOrtho_top_right
-/
theorem isOrtho_top_left {V : Submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥ :=
  isOrtho_comm.trans isOrtho_top_right

/--
theorem `IsOrtho.disjoint` / 定理 `IsOrtho.disjoint`

English:
theorem IsOrtho.disjoint
  given: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  statement: Disjoint U V
  proof: (Submodule.orthogonal_disjoint _).mono_right h.symm

@[simp]

中文:
定理 IsOrtho.disjoint
  条件: {U V : Submodule 𝕜 E} (h : U ⟂ V)
  结论: Disjoint U V
  证明: (Submodule.orthogonal_disjoint _).mono_right h.symm

@[simp]

Depends on / 依赖: Submodule, Submodule.orthogonal_disjoint, h.symm, mono_right, orthogonal_disjoint
-/
theorem IsOrtho.disjoint {U V : Submodule 𝕜 E} (h : U ⟂ V) : Disjoint U V :=
  (Submodule.orthogonal_disjoint _).mono_right h.symm

@[simp]
/--
theorem `isOrtho_sup_left` / 定理 `isOrtho_sup_left`

English:
theorem isOrtho_sup_left
  given: {U₁ U₂ V : Submodule 𝕜 E}
  statement: U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V
  proof: sup_le_iff

@[simp]

中文:
定理 isOrtho_sup_left
  条件: {U₁ U₂ V : Submodule 𝕜 E}
  结论: U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V
  证明: sup_le_iff

@[simp]

Depends on / 依赖: sup_le_iff
-/
theorem isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V :=
  sup_le_iff

@[simp]
/--
theorem `isOrtho_sup_right` / 定理 `isOrtho_sup_right`

English:
theorem isOrtho_sup_right
  given: {U V₁ V₂ : Submodule 𝕜 E}
  statement: U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂
  proof: isOrtho_comm.trans isOrtho_sup_left.trans isOrtho_comm.and isOrtho_comm

@[simp]

中文:
定理 isOrtho_sup_right
  条件: {U V₁ V₂ : Submodule 𝕜 E}
  结论: U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂
  证明: isOrtho_comm.trans isOrtho_sup_left.trans isOrtho_comm.and isOrtho_comm

@[simp]

Depends on / 依赖: isOrtho_comm, isOrtho_comm.and, isOrtho_comm.trans, isOrtho_sup_left, isOrtho_sup_left.trans
-/
theorem isOrtho_sup_right {U V₁ V₂ : Submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂ :=
isOrtho_comm.trans isOrtho_sup_left.trans isOrtho_comm.and isOrtho_comm

@[simp]
/--
theorem `isOrtho_sSup_left` / 定理 `isOrtho_sSup_left`

English:
theorem isOrtho_sSup_left
  given: {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E}
  proof: sSup_le_iff

@[simp]

中文:
定理 isOrtho_sSup_left
  条件: {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E}
  证明: sSup_le_iff

@[simp]

Depends on / 依赖: sSup_le_iff
-/
theorem isOrtho_sSup_left {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E} :
    sSup U ⟂ V ↔ forall Uᵢ in U, Uᵢ ⟂ V :=
  sSup_le_iff

@[simp]
/--
theorem `isOrtho_sSup_right` / 定理 `isOrtho_sSup_right`

English:
theorem isOrtho_sSup_right
  given: {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)}
  proof: isOrtho_comm.trans isOrtho_sSup_left.trans by simp_rw [isOrtho_comm]

@[simp]

中文:
定理 isOrtho_sSup_right
  条件: {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)}
  证明: isOrtho_comm.trans isOrtho_sSup_left.trans by simp_rw [isOrtho_comm]

@[simp]

Depends on / 依赖: isOrtho_comm, isOrtho_comm.trans, isOrtho_sSup_left, isOrtho_sSup_left.trans, simp_rw
-/
theorem isOrtho_sSup_right {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)} :
    U ⟂ sSup V ↔ forall Vᵢ in V, U ⟂ Vᵢ :=
isOrtho_comm.trans isOrtho_sSup_left.trans by simp_rw [isOrtho_comm]

@[simp]
/--
theorem `isOrtho_iSup_left` / 定理 `isOrtho_iSup_left`

English:
theorem isOrtho_iSup_left
  given: {ι : Sort*} {U : ι -> Submodule 𝕜 E} {V : Submodule 𝕜 E}
  proof: iSup_le_iff

@[simp]

中文:
定理 isOrtho_iSup_left
  条件: {ι : Sort*} {U : ι -> Submodule 𝕜 E} {V : Submodule 𝕜 E}
  证明: iSup_le_iff

@[simp]

Depends on / 依赖: iSup_le_iff
-/
theorem isOrtho_iSup_left {ι : Sort*} {U : ι -> Submodule 𝕜 E} {V : Submodule 𝕜 E} :
    iSup U ⟂ V ↔ forall i, U i ⟂ V :=
  iSup_le_iff

@[simp]
/--
theorem `isOrtho_iSup_right` / 定理 `isOrtho_iSup_right`

English:
theorem isOrtho_iSup_right
  given: {ι : Sort*} {U : Submodule 𝕜 E} {V : ι -> Submodule 𝕜 E}
  proof: isOrtho_comm.trans isOrtho_iSup_left.trans by simp_rw [isOrtho_comm]

@[simp]

中文:
定理 isOrtho_iSup_right
  条件: {ι : Sort*} {U : Submodule 𝕜 E} {V : ι -> Submodule 𝕜 E}
  证明: isOrtho_comm.trans isOrtho_iSup_left.trans by simp_rw [isOrtho_comm]

@[simp]

Depends on / 依赖: isOrtho_comm, isOrtho_comm.trans, isOrtho_iSup_left, isOrtho_iSup_left.trans, simp_rw
-/
theorem isOrtho_iSup_right {ι : Sort*} {U : Submodule 𝕜 E} {V : ι -> Submodule 𝕜 E} :
    U ⟂ iSup V ↔ forall i, U ⟂ V i :=
isOrtho_comm.trans isOrtho_iSup_left.trans by simp_rw [isOrtho_comm]

@[simp]
/--
theorem `isOrtho_span` / 定理 `isOrtho_span`

English:
theorem isOrtho_span
  given: {s t : Set E}
  proof: by
  simp_rw [span_eq_iSup_of_singleton_spans s, span_eq_iSup_of_singleton_spans t, isOrtho_iSup_left,
    isOrtho_iSup_right, isOrtho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]

中文:
定理 isOrtho_span
  条件: {s t : Set E}
  证明: by
  simp_rw [span_eq_iSup_of_singleton_spans s, span_eq_iSup_of_singleton_spans t, isOrtho_iSup_left,
    isOrtho_iSup_right, isOrtho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]

Depends on / 依赖: Set.mem_singleton_iff, Set.subset_def, SetLike, SetLike.mem_coe, forall_eq, isOrtho_iSup_left, isOrtho_iSup_right, isOrtho_iff_le, mem_coe, mem_orthogonal_singleton_iff_inner_left, mem_singleton_iff, simp_rw, span_eq_iSup_of_singleton_spans, span_le, subset_def
-/
theorem isOrtho_span {s t : Set E} :
    span 𝕜 s ⟂ span 𝕜 t ↔ forall ⦃u⦄, u in s -> forall ⦃v⦄, v in t -> ⟪u, v⟫ = 0 := by
  simp_rw [span_eq_iSup_of_singleton_spans s, span_eq_iSup_of_singleton_spans t, isOrtho_iSup_left,
    isOrtho_iSup_right, isOrtho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]

/--
theorem `IsOrtho.map` / 定理 `IsOrtho.map`

English:
theorem IsOrtho.map
  given: (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V)
  proof: by
  aesop (add simp [isOrtho_iff_inner_eq])

中文:
定理 IsOrtho.map
  条件: (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V)
  证明: by
  aesop (add simp [isOrtho_iff_inner_eq])

Depends on / 依赖: isOrtho_iff_inner_eq
-/
theorem IsOrtho.map (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V) :
    U.map (f : E ->ₗ[𝕜] F) ⟂ V.map (f : E ->ₗ[𝕜] F) := by
  aesop (add simp [isOrtho_iff_inner_eq])

/--
theorem `IsOrtho.comap` / 定理 `IsOrtho.comap`

English:
theorem IsOrtho.comap
  given: (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V)
  proof: by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv

@[simp]

中文:
定理 IsOrtho.comap
  条件: (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V)
  证明: by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv

@[simp]

Depends on / 依赖: f.inner_map_map, inner_map_map, isOrtho_iff_inner_eq, mem_comap, simp_rw
-/
theorem IsOrtho.comap (f : E ->ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V) :
    U.comap (f : E ->ₗ[𝕜] F) ⟂ V.comap (f : E ->ₗ[𝕜] F) := by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv

@[simp]
/--
theorem `IsOrtho.map_iff` / 定理 `IsOrtho.map_iff`

English:
theorem IsOrtho.map_iff
  given: (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E}
  proof: by
  refine ⟨fun h => ?_, IsOrtho.map f.toLinearIsometry⟩
  have hf : forall p : Submodule 𝕜 E,
      (p.map (f : E ->ₗ[𝕜] F)).comap (f.toLinearIsometry : E ->ₗ[𝕜] F) = p :=
    comap_map_eq_of_injective f.injective
  simpa only [hf] using h.comap f.toLinearIsometry

@[simp]

中文:
定理 IsOrtho.map_iff
  条件: (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E}
  证明: by
  refine ⟨fun h => ?_, IsOrtho.map f.toLinearIsometry⟩
  have hf : forall p : Submodule 𝕜 E,
      (p.map (f : E ->ₗ[𝕜] F)).comap (f.toLinearIsometry : E ->ₗ[𝕜] F) = p :=
    comap_map_eq_of_injective f.injective
  simpa only [hf] using h.comap f.toLinearIsometry

@[simp]

Depends on / 依赖: IsOrtho, IsOrtho.map, Submodule, comap_map_eq_of_injective, f.injective, f.toLinearIsometry, h.comap, injective, p.map, toLinearIsometry
-/
theorem IsOrtho.map_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} :
    U.map (f : E ->ₗ[𝕜] F) ⟂ V.map (f : E ->ₗ[𝕜] F) ↔ U ⟂ V := by
  refine ⟨fun h => ?_, IsOrtho.map f.toLinearIsometry⟩
  have hf : forall p : Submodule 𝕜 E,
      (p.map (f : E ->ₗ[𝕜] F)).comap (f.toLinearIsometry : E ->ₗ[𝕜] F) = p :=
    comap_map_eq_of_injective f.injective
  simpa only [hf] using h.comap f.toLinearIsometry

@[simp]
/--
theorem `IsOrtho.comap_iff` / 定理 `IsOrtho.comap_iff`

English:
theorem IsOrtho.comap_iff
  given: (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F}
  proof: by
  convert IsOrtho.map_iff f.symm <;>
    exact Submodule.comap_equiv_eq_map_symm (f : E ≃ₗ[𝕜] F) _

中文:
定理 IsOrtho.comap_iff
  条件: (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F}
  证明: by
  convert IsOrtho.map_iff f.symm <;>
    exact Submodule.comap_equiv_eq_map_symm (f : E ≃ₗ[𝕜] F) _

Depends on / 依赖: IsOrtho, IsOrtho.map_iff, Submodule, Submodule.comap_equiv_eq_map_symm, comap_equiv_eq_map_symm, convert, f.symm, map_iff
-/
theorem IsOrtho.comap_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} :
    U.comap (f : E ->ₗ[𝕜] F) ⟂ V.comap (f : E ->ₗ[𝕜] F) ↔ U ⟂ V := by
  convert IsOrtho.map_iff f.symm <;>
    exact Submodule.comap_equiv_eq_map_symm (f : E ≃ₗ[𝕜] F) _

end Submodule

open scoped Function in -- required for scoped `on` notation
/--
theorem `orthogonalFamily_iff_pairwise` / 定理 `orthogonalFamily_iff_pairwise`

English:
theorem orthogonalFamily_iff_pairwise
  given: {ι} {V : ι -> Submodule 𝕜 E}
  proof: forall₃_congr fun _i _j _hij =>
Subtype.forall.trans
forall₂_congr fun _x _hx => Subtype.forall.trans
        forall₂_congr fun _y _hy => inner_eq_zero_symm

alias ⟨OrthogonalFamily.pairwise, OrthogonalFamily.of_pairwise⟩ := orthogonalFamily_iff_pairwise

中文:
定理 orthogonalFamily_iff_pairwise
  条件: {ι} {V : ι -> Submodule 𝕜 E}
  证明: forall₃_congr fun _i _j _hij =>
Subtype.forall.trans
forall₂_congr fun _x _hx => Subtype.forall.trans
        forall₂_congr fun _y _hy => inner_eq_zero_symm

alias ⟨OrthogonalFamily.pairwise, OrthogonalFamily.of_pairwise⟩ := orthogonalFamily_iff_pairwise

Depends on / 依赖: Subtype, Subtype.forall.trans, _hij, inner_eq_zero_symm
-/
theorem orthogonalFamily_iff_pairwise {ι} {V : ι -> Submodule 𝕜 E} :
    (OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) ↔ Pairwise ((· ⟂ ·) on V) :=
  forall₃_congr fun _i _j _hij =>
Subtype.forall.trans
forall₂_congr fun _x _hx => Subtype.forall.trans
        forall₂_congr fun _y _hy => inner_eq_zero_symm

alias ⟨OrthogonalFamily.pairwise, OrthogonalFamily.of_pairwise⟩ := orthogonalFamily_iff_pairwise

/--
theorem `OrthogonalFamily.isOrtho` / 定理 `OrthogonalFamily.isOrtho`

English:
theorem OrthogonalFamily.isOrtho
  statement: {ι} {V : ι -> Submodule 𝕜 E}
  proof: hV.pairwise hij

中文:
定理 OrthogonalFamily.isOrtho
  结论: {ι} {V : ι -> Submodule 𝕜 E}
  证明: hV.pairwise hij

Depends on / 依赖: hV.pairwise, pairwise
-/
theorem OrthogonalFamily.isOrtho {ι} {V : ι -> Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i j : ι} (hij : i != j) :
    V i ⟂ V j :=
  hV.pairwise hij

namespace ClosedSubmodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : ClosedSubmodule 𝕜 E)

/--
Definition of `orthogonal` / `orthogonal` 的定义

English:
definition orthogonal
  signature: : ClosedSubmodule 𝕜 E where
  body: K.toSubmodule.orthogonal
  isClosed' := K.toSubmodule.isClosed_orthogonal

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

@[simp]

中文:
定义 orthogonal
  签名: : ClosedSubmodule 𝕜 E where
  定义体: K.toSubmodule.orthogonal
  isClosed' := K.toSubmodule.isClosed_orthogonal

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

@[simp]

Depends on / 依赖: K.toSubmodule.orthogonal, orthogonal, toSubmodule
-/
def orthogonal : ClosedSubmodule 𝕜 E where
  toSubmodule := K.toSubmodule.orthogonal
  isClosed' := K.toSubmodule.isClosed_orthogonal

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

@[simp]
/--
lemma `toSubmodule_orthogonal_eq` / 引理 `toSubmodule_orthogonal_eq`

English:
lemma toSubmodule_orthogonal_eq
  statement: K.orthogonal.toSubmodule = K.toSubmodule.orthogonal
  proof: rfl

@[deprecated (since := "2026-01-18")] alias orthogonal_toSubmodule_eq := toSubmodule_orthogonal_eq

@[simp]

中文:
引理 toSubmodule_orthogonal_eq
  结论: K.orthogonal.toSubmodule = K.toSubmodule.orthogonal
  证明: rfl

@[deprecated (since := "2026-01-18")] alias orthogonal_toSubmodule_eq := toSubmodule_orthogonal_eq

@[simp]
-/
lemma toSubmodule_orthogonal_eq : K.orthogonal.toSubmodule = K.toSubmodule.orthogonal := rfl

@[deprecated (since := "2026-01-18")] alias orthogonal_toSubmodule_eq := toSubmodule_orthogonal_eq

@[simp]
/--
lemma `mem_orthogonal_toSubmodule_iff` / 引理 `mem_orthogonal_toSubmodule_iff`

English:
lemma mem_orthogonal_toSubmodule_iff
  given: (v : E)
  statement: v in (K.toSubmodule)ᗮ ↔ v in Kᗮ
  proof: Iff.rfl

@[deprecated (since := "2026-01-18")] alias mem_orthogonal_iff := mem_orthogonal_toSubmodule_iff

中文:
引理 mem_orthogonal_toSubmodule_iff
  条件: (v : E)
  结论: v in (K.toSubmodule)ᗮ ↔ v in Kᗮ
  证明: Iff.rfl

@[deprecated (since := "2026-01-18")] alias mem_orthogonal_iff := mem_orthogonal_toSubmodule_iff

Depends on / 依赖: Iff.rfl
-/
lemma mem_orthogonal_toSubmodule_iff (v : E) : v in (K.toSubmodule)ᗮ ↔ v in Kᗮ := Iff.rfl

@[deprecated (since := "2026-01-18")] alias mem_orthogonal_iff := mem_orthogonal_toSubmodule_iff

/-- When a vector is in `Kᗮ`. -/
@[simp]
/--
theorem `mem_orthogonal` / 定理 `mem_orthogonal`

English:
theorem mem_orthogonal
  given: (v : E)
  statement: v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0
  proof: Iff.rfl

中文:
定理 mem_orthogonal
  条件: (v : E)
  结论: v in Kᗮ ↔ 对任意 u in K, ⟪u, v⟫ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0 := Iff.rfl

/--
theorem `mem_orthogonal'` / 定理 `mem_orthogonal'`

English:
theorem mem_orthogonal'
  given: (v : E)
  statement: v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0
  proof: Submodule.mem_orthogonal' K.toSubmodule v

中文:
定理 mem_orthogonal'
  条件: (v : E)
  结论: v in Kᗮ ↔ 对任意 u in K, ⟪v, u⟫ = 0
  证明: Submodule.mem_orthogonal' K.toSubmodule v

Depends on / 依赖: K.toSubmodule, Submodule, Submodule.mem_orthogonal, mem_orthogonal, toSubmodule
-/
theorem mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0 :=
  Submodule.mem_orthogonal' K.toSubmodule v

variable {K}

/--
theorem `sub_mem_orthogonal_of_inner_left` / 定理 `sub_mem_orthogonal_of_inner_left`

English:
theorem sub_mem_orthogonal_of_inner_left
  given: {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫)
  statement: x - y in Kᗮ
  proof: Submodule.sub_mem_orthogonal_of_inner_left h

中文:
定理 sub_mem_orthogonal_of_inner_left
  条件: {x y : E} (h : 对任意 v : K, ⟪x, v⟫ = ⟪y, v⟫)
  结论: x - y in Kᗮ
  证明: Submodule.sub_mem_orthogonal_of_inner_left h

Depends on / 依赖: Submodule, Submodule.sub_mem_orthogonal_of_inner_left, sub_mem_orthogonal_of_inner_left
-/
theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y in Kᗮ :=
  Submodule.sub_mem_orthogonal_of_inner_left h

/--
theorem `sub_mem_orthogonal_of_inner_right` / 定理 `sub_mem_orthogonal_of_inner_right`

English:
theorem sub_mem_orthogonal_of_inner_right
  given: {x y : E} (h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫)
  proof: Submodule.sub_mem_orthogonal_of_inner_right h

中文:
定理 sub_mem_orthogonal_of_inner_right
  条件: {x y : E} (h : 对任意 v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫)
  证明: Submodule.sub_mem_orthogonal_of_inner_right h

Depends on / 依赖: Submodule, Submodule.sub_mem_orthogonal_of_inner_right, sub_mem_orthogonal_of_inner_right
-/
theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y in Kᗮ := Submodule.sub_mem_orthogonal_of_inner_right h

variable (K)

/--
theorem `inf_orthogonal_eq_bot` / 定理 `inf_orthogonal_eq_bot`

English:
theorem inf_orthogonal_eq_bot
  statement: K ⊓ Kᗮ = ⊥
  proof: by
  rw [eq_bot_iff]
  intro x
  simpa using fun hx ho => inner_self_eq_zero.1 (ho x hx)

中文:
定理 inf_orthogonal_eq_bot
  结论: K ⊓ Kᗮ = ⊥
  证明: by
  rw [eq_bot_iff]
  intro x
  simpa using fun hx ho => inner_self_eq_zero.1 (ho x hx)

Depends on / 依赖: eq_bot_iff, inner_self_eq_zero
-/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x
  simpa using fun hx ho => inner_self_eq_zero.1 (ho x hx)

/--
theorem `orthogonal_disjoint` / 定理 `orthogonal_disjoint`

English:
theorem orthogonal_disjoint
  statement: Disjoint K Kᗮ
  proof: by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

中文:
定理 orthogonal_disjoint
  结论: Disjoint K Kᗮ
  证明: by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

Depends on / 依赖: K.inf_orthogonal_eq_bot, disjoint_iff, inf_orthogonal_eq_bot
-/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/--
theorem `orthogonal_eq_inter` / 定理 `orthogonal_eq_inter`

English:
theorem orthogonal_eq_inter
  statement: Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)).toLinearMap
  proof: by
  ext
  simp

中文:
定理 orthogonal_eq_inter
  结论: Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)).toLinearMap
  证明: by
  ext
  simp
-/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)).toLinearMap := by
  ext
  simp

variable (𝕜 E)

/--
theorem `orthogonal_gc` / 定理 `orthogonal_gc`

English:
theorem orthogonal_gc
  proof: fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

中文:
定理 orthogonal_gc
  证明: fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

Depends on / 依赖: Submodule, Submodule.inner_left_of_mem_orthogonal, inner_left_of_mem_orthogonal
-/
theorem orthogonal_gc :
    @GaloisConnection (ClosedSubmodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal :=
  fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/--
theorem `orthogonal_le` / 定理 `orthogonal_le`

English:
theorem orthogonal_le
  given: {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂)
  statement: K₂ᗮ <= K₁ᗮ
  proof: (orthogonal_gc 𝕜 E).monotone_l h

中文:
定理 orthogonal_le
  条件: {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂)
  结论: K₂ᗮ <= K₁ᗮ
  证明: (orthogonal_gc 𝕜 E).monotone_l h

Depends on / 依赖: monotone_l, orthogonal_gc
-/
theorem orthogonal_le {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂) : K₂ᗮ <= K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h

/--
theorem `orthogonal_orthogonal_monotone` / 定理 `orthogonal_orthogonal_monotone`

English:
theorem orthogonal_orthogonal_monotone
  given: {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂)
  statement: K₁ᗮᗮ <= K₂ᗮᗮ
  proof: orthogonal_le (orthogonal_le h)

中文:
定理 orthogonal_orthogonal_monotone
  条件: {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂)
  结论: K₁ᗮᗮ <= K₂ᗮᗮ
  证明: orthogonal_le (orthogonal_le h)

Depends on / 依赖: orthogonal_le
-/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂) : K₁ᗮᗮ <= K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)

/--
theorem `inf_orthogonal` / 定理 `inf_orthogonal`

English:
theorem inf_orthogonal
  given: (K₁ K₂ : ClosedSubmodule 𝕜 E)
  statement: K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_sup.symm

中文:
定理 inf_orthogonal
  条件: (K₁ K₂ : ClosedSubmodule 𝕜 E)
  结论: K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_sup.symm

Depends on / 依赖: l_sup, l_sup.symm, orthogonal_gc
-/
theorem inf_orthogonal (K₁ K₂ : ClosedSubmodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm

/--
theorem `iInf_orthogonal` / 定理 `iInf_orthogonal`

English:
theorem iInf_orthogonal
  given: {ι : Type*} (K : ι -> ClosedSubmodule 𝕜 E)
  statement: ⨅ i, (K i)ᗮ = (iSup K)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_iSup.symm

中文:
定理 iInf_orthogonal
  条件: {ι : 类型} (K : ι -> ClosedSubmodule 𝕜 E)
  结论: ⨅ i, (K i)ᗮ = (iSup K)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_iSup.symm

Depends on / 依赖: l_iSup, l_iSup.symm, orthogonal_gc
-/
theorem iInf_orthogonal {ι : Type*} (K : ι -> ClosedSubmodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm

/--
theorem `sInf_orthogonal` / 定理 `sInf_orthogonal`

English:
theorem sInf_orthogonal
  given: (s : Set <| ClosedSubmodule 𝕜 E)
  statement: ⨅ K in s, Kᗮ = (sSup s)ᗮ
  proof: (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]

中文:
定理 sInf_orthogonal
  条件: (s : Set <| ClosedSubmodule 𝕜 E)
  结论: ⨅ K in s, Kᗮ = (sSup s)ᗮ
  证明: (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]

Depends on / 依赖: l_sSup, l_sSup.symm, orthogonal_gc
-/
theorem sInf_orthogonal (s : Set <| ClosedSubmodule 𝕜 E) : ⨅ K in s, Kᗮ = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]
/--
theorem `top_orthogonal_eq_bot` / 定理 `top_orthogonal_eq_bot`

English:
theorem top_orthogonal_eq_bot
  statement: (⊤ : ClosedSubmodule 𝕜 E)ᗮ = ⊥
  proof: by ext x; simp

@[simp]

中文:
定理 top_orthogonal_eq_bot
  结论: (⊤ : ClosedSubmodule 𝕜 E)ᗮ = ⊥
  证明: by ext x; simp

@[simp]
-/
theorem top_orthogonal_eq_bot : (⊤ : ClosedSubmodule 𝕜 E)ᗮ = ⊥ := by ext x; simp

@[simp]
/--
theorem `bot_orthogonal_eq_top` / 定理 `bot_orthogonal_eq_top`

English:
theorem bot_orthogonal_eq_top
  statement: (⊥ : ClosedSubmodule 𝕜 E)ᗮ = ⊤
  proof: by ext x; simp

@[simp]

中文:
定理 bot_orthogonal_eq_top
  结论: (⊥ : ClosedSubmodule 𝕜 E)ᗮ = ⊤
  证明: by ext x; simp

@[simp]
-/
theorem bot_orthogonal_eq_top : (⊥ : ClosedSubmodule 𝕜 E)ᗮ = ⊤ := by ext x; simp

@[simp]
/--
theorem `orthogonal_eq_top_iff` / 定理 `orthogonal_eq_top_iff`

English:
theorem orthogonal_eq_top_iff
  statement: Kᗮ = ⊤ ↔ K = ⊥
  proof: by
  refine
    ⟨?_, by rintro rfl; exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

中文:
定理 orthogonal_eq_top_iff
  结论: Kᗮ = ⊤ ↔ K = ⊥
  证明: by
  refine
    ⟨?_, by rintro rfl; exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

Depends on / 依赖: K.orthogonal_disjoint.eq_bot, bot_orthogonal_eq_top, eq_bot, inf_comm, orthogonal_disjoint, top_inf_eq
-/
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine
    ⟨?_, by rintro rfl; exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

/-- The orthogonal complement of the closure of a submodule (as a `Submodule`) is equal to
the orthogonal complement. -/
@[simp]
/--
lemma `orthogonal_closure` / 引理 `orthogonal_closure`

English:
lemma orthogonal_closure
  given: (K : Submodule 𝕜 E)
  statement: (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ
  proof: by
  rw [← Submodule.orthogonal_closure K]
  congr

中文:
引理 orthogonal_closure
  条件: (K : Submodule 𝕜 E)
  结论: (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ
  证明: by
  rw [← Submodule.orthogonal_closure K]
  congr

Depends on / 依赖: Submodule, Submodule.orthogonal_closure, orthogonal_closure
-/
lemma orthogonal_closure (K : Submodule 𝕜 E) : (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ := by
  rw [← Submodule.orthogonal_closure K]
  congr

/--
lemma `orthogonal_closure'` / 引理 `orthogonal_closure'`

English:
lemma orthogonal_closure'
  given: (K : Submodule 𝕜 E)
  statement: K.closureᗮ = ⟨Kᗮ, K.isClosed_orthogonal⟩
  proof: by
  ext x; simp

中文:
引理 orthogonal_closure'
  条件: (K : Submodule 𝕜 E)
  结论: K.closureᗮ = ⟨Kᗮ, K.isClosed_orthogonal⟩
  证明: by
  ext x; simp
-/
lemma orthogonal_closure' (K : Submodule 𝕜 E) : K.closureᗮ = ⟨Kᗮ, K.isClosed_orthogonal⟩ := by
  ext x; simp

/--
lemma `orthogonal_closure''` / 引理 `orthogonal_closure''`

English:
lemma orthogonal_closure''
  given: (K : Submodule 𝕜 E)
  statement: K.closureᗮ = Kᗮ.closure
  proof: by
  rw [Submodule.closure_eq' K.isClosed_orthogonal]
  exact orthogonal_closure' K

中文:
引理 orthogonal_closure''
  条件: (K : Submodule 𝕜 E)
  结论: K.closureᗮ = Kᗮ.closure
  证明: by
  rw [Submodule.closure_eq' K.isClosed_orthogonal]
  exact orthogonal_closure' K

Depends on / 依赖: K.isClosed_orthogonal, Submodule, Submodule.closure_eq, closure_eq, isClosed_orthogonal, orthogonal_closure
-/
lemma orthogonal_closure'' (K : Submodule 𝕜 E) : K.closureᗮ = Kᗮ.closure := by
  rw [Submodule.closure_eq' K.isClosed_orthogonal]
  exact orthogonal_closure' K

end ClosedSubmodule
