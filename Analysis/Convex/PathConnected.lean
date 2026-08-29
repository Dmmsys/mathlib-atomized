/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Connected.PathConnected

/-!
# Segment between 2 points as a bundled path

In this file we define `Path.segment a b : Path a b`
to be the path going from `a` to `b` along the straight segment with constant velocity `b - a`.

We also prove basic properties of this construction,
then use it to show that a nonempty convex set is path connected.
In particular, a topological vector space over `ℝ` is path connected.
-/

@[expose] public section

open AffineMap Set
open scoped Convex unitInterval

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul Real E]

namespace Path

set_option backward.isDefEq.respectTransparency false in
/-- The path from `a` to `b` going along a straight line segment -/
@[simps]
/--
Definition of `segment` / `segment` 的定义

English:
definition segment
  signature: (a b : E)
  body: lineMap a b (t : Real)
  continuous_toFun := by dsimp [lineMap]; fun_prop
  source' := by simp
  target' := by simp

@[simp]

中文:
定义 segment
  签名: (a b : E)
  定义体: lineMap a b (t : Real)
  continuous_toFun := by dsimp [lineMap]; fun_prop
  source' := by simp
  target' := by simp

@[simp]
-/
protected def segment (a b : E) : Path a b where
  toFun t := lineMap a b (t : Real)
  continuous_toFun := by dsimp [lineMap]; fun_prop
  source' := by simp
  target' := by simp

@[simp]
/--
theorem `range_segment` / 定理 `range_segment`

English:
theorem range_segment
  given: (a b : E)
  statement: Set.range (Path.segment a b) = [a -[Real] b]
  proof: by
  rw [segment_eq_image_lineMap]; rw [image_eq_range]
  simp only [← segment_apply]

@[simp]

中文:
定理 range_segment
  条件: (a b : E)
  结论: 集合.range (道路.segment a b) = [a -[实数] b]
  证明: by
  rw [segment_eq_image_lineMap]; rw [image_eq_range]
  simp only [← segment_apply]

@[simp]

Depends on / 依赖: image_eq_range, segment_apply, segment_eq_image_lineMap
-/
theorem range_segment (a b : E) : Set.range (Path.segment a b) = [a -[Real] b] := by
  rw [segment_eq_image_lineMap]; rw [image_eq_range]
  simp only [← segment_apply]

@[simp]
/--
theorem `segment_same` / 定理 `segment_same`

English:
theorem segment_same
  given: (a : E)
  statement: Path.segment a a = .refl a
  proof: by ext; simp

@[simp]

中文:
定理 segment_same
  条件: (a : E)
  结论: 道路.segment a a = .refl a
  证明: by ext; simp

@[simp]
-/
protected theorem segment_same (a : E) : Path.segment a a = .refl a := by ext; simp

@[simp]
/--
theorem `segment_symm` / 定理 `segment_symm`

English:
theorem segment_symm
  given: (a b : E)
  statement: (Path.segment a b).symm = .segment b a
  proof: by
  ext; simp

@[simp]

中文:
定理 segment_symm
  条件: (a b : E)
  结论: (道路.segment a b).symm = .segment b a
  证明: by
  ext; simp

@[simp]
-/
protected theorem segment_symm (a b : E) : (Path.segment a b).symm = .segment b a := by
  ext; simp

@[simp]
/--
theorem `segment_add_segment` / 定理 `segment_add_segment`

English:
theorem segment_add_segment
  given: (a b c d : E)
  proof: by
  ext
  simp [lineMap_apply_module, add_add_add_comm]

@[simp]

中文:
定理 segment_add_segment
  条件: (a b c d : E)
  证明: by
  ext
  simp [lineMap_apply_module, add_add_add_comm]

@[simp]

Depends on / 依赖: add_add_add_comm, lineMap_apply_module
-/
theorem segment_add_segment (a b c d : E) :
    (Path.segment a b).add (.segment c d) = .segment (a + c) (b + d) := by
  ext
  simp [lineMap_apply_module, add_add_add_comm]

@[simp]
/--
theorem `cast_segment` / 定理 `cast_segment`

English:
theorem cast_segment
  given: {a b c d : E} (hac : c = a) (hbd : d = b)
  proof: by
  subst_vars; rfl

中文:
定理 cast_segment
  条件: {a b c d : E} (hac : c = a) (hbd : d = b)
  证明: by
  subst_vars; rfl
-/
theorem cast_segment {a b c d : E} (hac : c = a) (hbd : d = b) :
    (Path.segment a b).cast hac hbd = .segment c d := by
  subst_vars; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eqOn_extend_segment` / 定理 `eqOn_extend_segment`

English:
theorem eqOn_extend_segment
  given: (a b : E)
  proof: by
  intro t ht
  simp [ht]

中文:
定理 eqOn_extend_segment
  条件: (a b : E)
  证明: by
  intro t ht
  simp [ht]
-/
theorem eqOn_extend_segment (a b : E) :
    EqOn (Path.segment a b).extend (AffineMap.lineMap a b) I := by
  intro t ht
  simp [ht]

/--
theorem `segment_injective_of_ne` / 定理 `segment_injective_of_ne`

English:
theorem segment_injective_of_ne
  given: {a b : E} (hne : a != b)
  proof: (lineMap_injective _ hne).comp Subtype.coe_injective

中文:
定理 segment_injective_of_ne
  条件: {a b : E} (hne : a != b)
  证明: (lineMap_injective _ hne).comp Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, lineMap_injective
-/
theorem segment_injective_of_ne {a b : E} (hne : a != b) :
    Function.Injective (Path.segment a b) := (lineMap_injective _ hne).comp Subtype.coe_injective

end Path

/--
theorem `JoinedIn.of_segment_subset` / 定理 `JoinedIn.of_segment_subset`

English:
theorem JoinedIn.of_segment_subset
  given: {x y : E} {s : Set E} (h : [x -[Real] y] subseteq s)
  statement: JoinedIn s x y
  proof: by
  use .segment x y
  rwa [← range_subset_iff, Path.range_segment]

中文:
定理 JoinedIn.of_segment_subset
  条件: {x y : E} {s : 集合 E} (h : [x -[实数] y] subseteq s)
  结论: JoinedIn s x y
  证明: by
  use .segment x y
  rwa [← range_subset_iff, Path.range_segment]

Depends on / 依赖: Path.range_segment, range_segment, range_subset_iff, segment
-/
theorem JoinedIn.of_segment_subset {x y : E} {s : Set E} (h : [x -[Real] y] subseteq s) : JoinedIn s x y := by
  use .segment x y
  rwa [← range_subset_iff, Path.range_segment]

/--
theorem `StarConvex.isPathConnected` / 定理 `StarConvex.isPathConnected`

English:
theorem StarConvex.isPathConnected
  statement: {s : Set E} {a : E} (h : StarConvex Real a s)
  proof: ⟨a, ha, fun _y hy => .of_segment_subset h.segment_subset hy⟩

中文:
定理 StarConvex.isPathConnected
  结论: {s : 集合 E} {a : E} (h : StarConvex 实数 a s)
  证明: ⟨a, ha, fun _y hy => .of_segment_subset h.segment_subset hy⟩
-/
protected theorem StarConvex.isPathConnected {s : Set E} {a : E} (h : StarConvex Real a s)
    (ha : a in s) : IsPathConnected s :=
⟨a, ha, fun _y hy => .of_segment_subset h.segment_subset hy⟩

/--
theorem `Convex.isPathConnected` / 定理 `Convex.isPathConnected`

English:
theorem Convex.isPathConnected
  given: {s : Set E} (hconv : Convex Real s) (hne : s.Nonempty)
  proof: let ⟨_a, ha⟩ := hne; (hconv ha).isPathConnected ha

中文:
定理 凸.isPathConnected
  条件: {s : 集合 E} (hconv : 凸 实数 s) (hne : s.非空)
  证明: let ⟨_a, ha⟩ := hne; (hconv ha).isPathConnected ha
-/
protected theorem Convex.isPathConnected {s : Set E} (hconv : Convex Real s) (hne : s.Nonempty) :
    IsPathConnected s :=
  let ⟨_a, ha⟩ := hne; (hconv ha).isPathConnected ha

/--
theorem `Convex.isConnected` / 定理 `Convex.isConnected`

English:
theorem Convex.isConnected
  given: {s : Set E} (h : Convex Real s) (hne : s.Nonempty)
  proof: (h.isPathConnected hne).isConnected

中文:
定理 凸.isConnected
  条件: {s : 集合 E} (h : 凸 实数 s) (hne : s.非空)
  证明: (h.isPathConnected hne).isConnected
-/
protected theorem Convex.isConnected {s : Set E} (h : Convex Real s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.isPathConnected hne).isConnected

/--
theorem `Convex.isPreconnected` / 定理 `Convex.isPreconnected`

English:
theorem Convex.isPreconnected
  given: {s : Set E} (h : Convex Real s)
  statement: IsPreconnected s
  proof: s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected

中文:
定理 凸.isPreconnected
  条件: {s : 集合 E} (h : 凸 实数 s)
  结论: 是预连通 s
  证明: s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected
-/
protected theorem Convex.isPreconnected {s : Set E} (h : Convex Real s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected

/--
theorem `Submodule.isPathConnected` / 定理 `Submodule.isPathConnected`

English:
theorem Submodule.isPathConnected
  given: (s : Submodule Real E)
  statement: IsPathConnected (s : Set E)
  proof: s.convex.isPathConnected s.nonempty

中文:
定理 子模.isPathConnected
  条件: (s : 子模 实数 E)
  结论: 是道路连通 (s : 集合 E)
  证明: s.convex.isPathConnected s.nonempty

Depends on / 依赖: convex, isPathConnected, nonempty, s.convex.isPathConnected, s.nonempty
-/
theorem Submodule.isPathConnected (s : Submodule Real E) : IsPathConnected (s : Set E) :=
  s.convex.isPathConnected s.nonempty

/--
theorem `IsTopologicalAddGroup.pathConnectedSpace` / 定理 `IsTopologicalAddGroup.pathConnectedSpace`

English:
theorem IsTopologicalAddGroup.pathConnectedSpace
  statement: PathConnectedSpace E
  proof: pathConnectedSpace_iff_univ.mpr convex_univ.isPathConnected ⟨(0 : E), trivial⟩

中文:
定理 是拓扑加群.pathConnectedSpace
  结论: 道路连通空间 E
  证明: pathConnectedSpace_iff_univ.mpr convex_univ.isPathConnected ⟨(0 : E), trivial⟩

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.refl, ofRepr
-/
protected theorem IsTopologicalAddGroup.pathConnectedSpace : PathConnectedSpace E :=
pathConnectedSpace_iff_univ.mpr convex_univ.isPathConnected ⟨(0 : E), trivial⟩

/--
theorem `isPathConnected_compl_of_isPathConnected_compl_zero` / 定理 `isPathConnected_compl_of_isPathConnected_compl_zero`

English:
theorem isPathConnected_compl_of_isPathConnected_compl_zero
  statement: {p q : Submodule Real E}
  proof: by
  convert (hpc.image continuous_subtype_val).add q.isPathConnected
  trans Submodule.prodEquivOfIsCompl p q hpq '' ({0}ᶜ ×ˢ univ)
  · rw [prod_univ, LinearEquiv.image_eq_preimage_symm]
    ext
    simp
  · ext
    simp [mem_add, and_assoc]

中文:
定理 isPathConnected_compl_of_isPathConnected_compl_zero
  结论: {p q : 子模 实数 E}
  证明: by
  convert (hpc.image continuous_subtype_val).add q.isPathConnected
  trans Submodule.prodEquivOfIsCompl p q hpq '' ({0}ᶜ ×ˢ univ)
  · rw [prod_univ, LinearEquiv.image_eq_preimage_symm]
    ext
    simp
  · ext
    simp [mem_add, and_assoc]

Depends on / 依赖: LinearEquiv, LinearEquiv.image_eq_preimage_symm, Submodule, Submodule.prodEquivOfIsCompl, and_assoc, continuous_subtype_val, convert, hpc.image, image_eq_preimage_symm, isPathConnected, mem_add, prodEquivOfIsCompl, prod_univ, q.isPathConnected
-/
theorem isPathConnected_compl_of_isPathConnected_compl_zero {p q : Submodule Real E}
    (hpq : IsCompl p q) (hpc : IsPathConnected ({0}ᶜ : Set p)) : IsPathConnected (qᶜ : Set E) := by
  convert (hpc.image continuous_subtype_val).add q.isPathConnected
  trans Submodule.prodEquivOfIsCompl p q hpq '' ({0}ᶜ ×ˢ univ)
  · rw [prod_univ, LinearEquiv.image_eq_preimage_symm]
    ext
    simp
  · ext
    simp [mem_add, and_assoc]

section Real

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `segment_image_Ico` / 定理 `segment_image_Ico`

English:
theorem segment_image_Ico
  given: {x y : Real} (h : x < y)
  statement: (Path.segment x y) '' Ico 0 1 = Ico x y
  proof: by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ico 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ico,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ico (sub_pos_of_lt h) x 0 1 using 2 <;> ring

中文:
定理 segment_image_Ico
  条件: {x y : 实数} (h : x < y)
  结论: (道路.segment x y) '' 左闭右开区间 0 1 = 左闭右开区间 x y
  证明: by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ico 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ico,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ico (sub_pos_of_lt h) x 0 1 using 2 <;> ring

Depends on / 依赖: Icc.coe_one, Icc.coe_zero, Path.segment_apply, Subtype, Subtype.val, coe_one, coe_zero, convert, image_affine_Ico, image_image, image_subtype_val_Ico, lineMap_apply, segment_apply, simp_rw, smul_eq_mul, sub_pos_of_lt, vadd_eq_add, vsub_eq_sub
-/
theorem segment_image_Ico {x y : Real} (h : x < y) : (Path.segment x y) '' Ico 0 1 = Ico x y := by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ico 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ico,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ico (sub_pos_of_lt h) x 0 1 using 2 <;> ring

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `segment_image_Ioc` / 定理 `segment_image_Ioc`

English:
theorem segment_image_Ioc
  given: {x y : Real} (h : x < y)
  statement: (Path.segment x y) '' Ioc 0 1 = Ioc x y
  proof: by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ioc 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ioc,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ioc (sub_pos_of_lt h) x 0 1 using 2 <;> ring

中文:
定理 segment_image_Ioc
  条件: {x y : 实数} (h : x < y)
  结论: (道路.segment x y) '' 左开右闭区间 0 1 = 左开右闭区间 x y
  证明: by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ioc 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ioc,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ioc (sub_pos_of_lt h) x 0 1 using 2 <;> ring

Depends on / 依赖: Icc.coe_one, Icc.coe_zero, Path.segment_apply, Subtype, Subtype.val, coe_one, coe_zero, convert, image_affine_Ioc, image_image, image_subtype_val_Ioc, lineMap_apply, segment_apply, simp_rw, smul_eq_mul, sub_pos_of_lt, vadd_eq_add, vsub_eq_sub
-/
theorem segment_image_Ioc {x y : Real} (h : x < y) : (Path.segment x y) '' Ioc 0 1 = Ioc x y := by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ioc 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ioc,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ioc (sub_pos_of_lt h) x 0 1 using 2 <;> ring

end Real
