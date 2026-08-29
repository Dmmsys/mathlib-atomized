/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Products of pseudometric spaces and other constructions

This file constructs the supremum distance on binary products of pseudometric spaces and provides
instances for type synonyms.
-/

@[expose] public section

open Bornology Filter Metric Set Topology
open scoped NNReal

variable {α β : Type*} [PseudoMetricSpace α]

/--
Definition of `PseudoMetricSpace.induced` / `PseudoMetricSpace.induced` 的定义

English:
abbreviation PseudoMetricSpace.induced
  signature: {α β} (f : α -> β) (m : PseudoMetricSpace β)
  body: dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_ofPred]

中文:
缩写 伪度量空间.induced
  签名: {α β} (f : α -> β) (m : 伪度量空间 β)
  定义体: dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_ofPred]
-/
abbrev PseudoMetricSpace.induced {α β} (f : α -> β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_ofPred]

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
@[instance_reducible]
/--
Definition of `Topology.IsInducing.comapPseudoMetricSpace` / `Topology.IsInducing.comapPseudoMetricSpace` 的定义

English:
definition Topology.IsInducing.comapPseudoMetricSpace
  signature: {α β : Type*} [TopologicalSpace α]
  body: .replaceTopology (.induced f m) hf.eq_induced

中文:
定义 拓扑.是Inducing.comapPseudoMetricSpace
  签名: {α β : 类型} [拓扑空间 α]
  定义体: .replaceTopology (.induced f m) hf.eq_induced

Depends on / 依赖: eq_induced, hf.eq_induced, induced, replaceTopology
-/
def Topology.IsInducing.comapPseudoMetricSpace {α β : Type*} [TopologicalSpace α]
    [m : PseudoMetricSpace β] {f : α -> β} (hf : IsInducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.eq_induced

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
@[instance_reducible]
/--
Definition of `IsUniformInducing.comapPseudoMetricSpace` / `IsUniformInducing.comapPseudoMetricSpace` 的定义

English:
definition IsUniformInducing.comapPseudoMetricSpace
  signature: {α β} [UniformSpace α] [m : PseudoMetricSpace β]
  body: .replaceUniformity (.induced f m) h.comap_uniformity.symm

中文:
定义 是UniformInducing.comapPseudoMetricSpace
  签名: {α β} [一致空间 α] [m : 伪度量空间 β]
  定义体: .replaceUniformity (.induced f m) h.comap_uniformity.symm

Depends on / 依赖: comap_uniformity, h.comap_uniformity.symm, induced, replaceUniformity
-/
def IsUniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α -> β) (h : IsUniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm

namespace Subtype

variable {p : α -> Prop}

/--
Instance `pseudoMetricSpace` / 实例 `pseudoMetricSpace`

English:
instance pseudoMetricSpace
  signature: : PseudoMetricSpace (Subtype p)
  body: PseudoMetricSpace.induced Subtype.val ‹_›

中文:
实例 pseudoMetricSpace
  签名: : 伪度量空间 (子类型 p)
  定义体: PseudoMetricSpace.induced Subtype.val ‹_›

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.induced, Subtype, Subtype.val, induced
-/
instance pseudoMetricSpace : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced Subtype.val ‹_›

/--
lemma `dist_eq` / 引理 `dist_eq`

English:
lemma dist_eq
  given: (x y : Subtype p)
  statement: dist x y = dist (x : α) y
  proof: rfl

中文:
引理 dist_eq
  条件: (x y : 子类型 p)
  结论: dist x y = dist (x : α) y
  证明: rfl
-/
lemma dist_eq (x y : Subtype p) : dist x y = dist (x : α) y := rfl

/--
lemma `nndist_eq` / 引理 `nndist_eq`

English:
lemma nndist_eq
  given: (x y : Subtype p)
  statement: nndist x y = nndist (x : α) y
  proof: rfl

@[simp]

中文:
引理 nndist_eq
  条件: (x y : 子类型 p)
  结论: nndist x y = nndist (x : α) y
  证明: rfl

@[simp]
-/
lemma nndist_eq (x y : Subtype p) : nndist x y = nndist (x : α) y := rfl

@[simp]
/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (a : {a // p a}) (r : Real)
  statement: Subtype.val ⁻¹' (ball a.1 r) = ball a r
  proof: rfl

@[simp]

中文:
定理 preimage_ball
  条件: (a : {a // p a}) (r : 实数)
  结论: 子类型.val ⁻¹' (ball a.1 r) = ball a r
  证明: rfl

@[simp]
-/
theorem preimage_ball (a : {a // p a}) (r : Real) : Subtype.val ⁻¹' (ball a.1 r) = ball a r :=
  rfl

@[simp]
/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: {p : α -> Prop} (a : {a // p a}) (r : Real)
  proof: rfl

@[simp]

中文:
定理 preimage_closedBall
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数)
  证明: rfl

@[simp]
-/
theorem preimage_closedBall {p : α -> Prop} (a : {a // p a}) (r : Real) :
    Subtype.val ⁻¹' (closedBall a.1 r) = closedBall a r :=
  rfl

@[simp]
/--
theorem `image_ball` / 定理 `image_ball`

English:
theorem image_ball
  given: {p : α -> Prop} (a : {a // p a}) (r : Real)
  proof: by
  rw [← preimage_ball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[simp]

中文:
定理 image_ball
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数)
  证明: by
  rw [← preimage_ball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[simp]

Depends on / 依赖: image_preimage_eq_inter_range, preimage_ball, range_val_subtype
-/
theorem image_ball {p : α -> Prop} (a : {a // p a}) (r : Real) :
    Subtype.val '' (ball a r) = ball a.1 r inter {a | p a} := by
  rw [← preimage_ball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[simp]
/--
theorem `image_closedBall` / 定理 `image_closedBall`

English:
theorem image_closedBall
  given: {p : α -> Prop} (a : {a // p a}) (r : Real)
  proof: by
  rw [← preimage_closedBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

中文:
定理 image_closedBall
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数)
  证明: by
  rw [← preimage_closedBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

Depends on / 依赖: image_preimage_eq_inter_range, preimage_closedBall, range_val_subtype
-/
theorem image_closedBall {p : α -> Prop} (a : {a // p a}) (r : Real) :
    Subtype.val '' (closedBall a r) = closedBall a.1 r inter {a | p a} := by
  rw [← preimage_closedBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

end Subtype

namespace MulOpposite

@[to_additive]
/--
Instance `instPseudoMetricSpace` / 实例 `instPseudoMetricSpace`

English:
instance instPseudoMetricSpace
  signature: : PseudoMetricSpace αᵐᵒᵖ
  body: PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]

中文:
实例 instPseudoMetricSpace
  签名: : 伪度量空间 αᵐᵒᵖ
  定义体: PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.unop, PseudoMetricSpace, PseudoMetricSpace.induced, induced
-/
instance instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]
/--
lemma `dist_unop` / 引理 `dist_unop`

English:
lemma dist_unop
  given: (x y : αᵐᵒᵖ)
  statement: dist (unop x) (unop y) = dist x y
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 dist_unop
  条件: (x y : αᵐᵒᵖ)
  结论: dist (unop x) (unop y) = dist x y
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl

@[to_additive (attr := simp)]
/--
lemma `dist_op` / 引理 `dist_op`

English:
lemma dist_op
  given: (x y : α)
  statement: dist (op x) (op y) = dist x y
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 dist_op
  条件: (x y : α)
  结论: dist (op x) (op y) = dist x y
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl

@[to_additive (attr := simp)]
/--
lemma `nndist_unop` / 引理 `nndist_unop`

English:
lemma nndist_unop
  given: (x y : αᵐᵒᵖ)
  statement: nndist (unop x) (unop y) = nndist x y
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 nndist_unop
  条件: (x y : αᵐᵒᵖ)
  结论: nndist (unop x) (unop y) = nndist x y
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl

@[to_additive (attr := simp)]
/--
lemma `nndist_op` / 引理 `nndist_op`

English:
lemma nndist_op
  given: (x y : α)
  statement: nndist (op x) (op y) = nndist x y
  proof: rfl

中文:
引理 nndist_op
  条件: (x y : α)
  结论: nndist (op x) (op y) = nndist x y
  证明: rfl
-/
lemma nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl

end MulOpposite

section NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace Real>=0
  body: inferInstanceAs PseudoMetricSpace (Subtype _)

中文:
实例 :
  签名: 伪度量空间 实数>=0
  定义体: inferInstanceAs PseudoMetricSpace (Subtype _)

Depends on / 依赖: PseudoMetricSpace, Subtype
-/
instance : PseudoMetricSpace Real>=0 :=
inferInstanceAs PseudoMetricSpace (Subtype _)

/--
lemma `NNReal.dist_eq` / 引理 `NNReal.dist_eq`

English:
lemma NNReal.dist_eq
  given: (a b : Real>=0)
  statement: dist a b = |(a : Real) - b|
  proof: rfl

中文:
引理 非负实数.dist_eq
  条件: (a b : 实数>=0)
  结论: dist a b = |(a : 实数) - b|
  证明: rfl
-/
lemma NNReal.dist_eq (a b : Real>=0) : dist a b = |(a : Real) - b| := rfl

/--
lemma `NNReal.nndist_eq` / 引理 `NNReal.nndist_eq`

English:
lemma NNReal.nndist_eq
  given: (a b : Real>=0)
  statement: nndist a b = max (a - b) (b - a)
  proof: eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := Real>=0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]

中文:
引理 非负实数.nndist_eq
  条件: (a b : 实数>=0)
  结论: nndist a b = 最大值 (a - b) (b - a)
  证明: eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := Real>=0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.coe_le_coe, abs_sub_le_iff, coe_add, coe_le_coe, coe_nndist, dist_eq, eq_of_forall_ge_iff, max_le_iff, tsub_le_iff_right
-/
lemma NNReal.nndist_eq (a b : Real>=0) : nndist a b = max (a - b) (b - a) :=
  eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := Real>=0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]
/--
lemma `NNReal.nndist_zero_eq_val` / 引理 `NNReal.nndist_zero_eq_val`

English:
lemma NNReal.nndist_zero_eq_val
  given: (z : Real>=0)
  statement: nndist 0 z = z
  proof: by
  simp [NNReal.nndist_eq]

@[simp]

中文:
引理 非负实数.nndist_zero_eq_val
  条件: (z : 实数>=0)
  结论: nndist 0 z = z
  证明: by
  simp [NNReal.nndist_eq]

@[simp]

Depends on / 依赖: NNReal, NNReal.nndist_eq, nndist_eq
-/
lemma NNReal.nndist_zero_eq_val (z : Real>=0) : nndist 0 z = z := by
  simp [NNReal.nndist_eq]

@[simp]
/--
lemma `NNReal.nndist_zero_eq_val'` / 引理 `NNReal.nndist_zero_eq_val'`

English:
lemma NNReal.nndist_zero_eq_val'
  given: (z : Real>=0)
  statement: nndist z 0 = z
  proof: by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z

中文:
引理 非负实数.nndist_zero_eq_val'
  条件: (z : 实数>=0)
  结论: nndist z 0 = z
  证明: by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z

Depends on / 依赖: NNReal, NNReal.nndist_zero_eq_val, nndist_comm, nndist_zero_eq_val
-/
lemma NNReal.nndist_zero_eq_val' (z : Real>=0) : nndist z 0 = z := by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z

/--
lemma `NNReal.le_add_nndist` / 引理 `NNReal.le_add_nndist`

English:
lemma NNReal.le_add_nndist
  given: (a b : Real>=0)
  statement: a <= b + nndist a b
  proof: by
  suffices (a : Real) <= (b : Real) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge

中文:
引理 非负实数.le_add_nndist
  条件: (a b : 实数>=0)
  结论: a <= b + nndist a b
  证明: by
  suffices (a : Real) <= (b : Real) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.coe_le_coe, coe_add, coe_le_coe, coe_nndist, dist_eq, le_of_abs_le, sub_le_iff_le_add
-/
lemma NNReal.le_add_nndist (a b : Real>=0) : a <= b + nndist a b := by
  suffices (a : Real) <= (b : Real) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge

/--
lemma `NNReal.ball_zero_eq_Ico'` / 引理 `NNReal.ball_zero_eq_Ico'`

English:
lemma NNReal.ball_zero_eq_Ico'
  given: (c : Real>=0)
  proof: by ext x; simp

中文:
引理 非负实数.ball_zero_eq_Ico'
  条件: (c : 实数>=0)
  证明: by ext x; simp
-/
lemma NNReal.ball_zero_eq_Ico' (c : Real>=0) :
    Metric.ball (0 : Real>=0) c.toReal = Set.Ico 0 c := by ext x; simp

/--
lemma `NNReal.ball_zero_eq_Ico` / 引理 `NNReal.ball_zero_eq_Ico`

English:
lemma NNReal.ball_zero_eq_Ico
  given: (c : Real)
  proof: by
  by_cases! c_pos : 0 < c
  · convert! NNReal.ball_zero_eq_Ico' (NNReal.mk c c_pos.le)
    simp [Real.toNNReal, c_pos.le]
  simp [c_pos]

中文:
引理 非负实数.ball_zero_eq_Ico
  条件: (c : 实数)
  证明: by
  by_cases! c_pos : 0 < c
  · convert! NNReal.ball_zero_eq_Ico' (NNReal.mk c c_pos.le)
    simp [Real.toNNReal, c_pos.le]
  simp [c_pos]

Depends on / 依赖: NNReal, NNReal.ball_zero_eq_Ico, NNReal.mk, Real.toNNReal, ball_zero_eq_Ico, c_pos, c_pos.le, convert, toNNReal
-/
lemma NNReal.ball_zero_eq_Ico (c : Real) :
    Metric.ball (0 : Real>=0) c = Set.Ico 0 c.toNNReal := by
  by_cases! c_pos : 0 < c
  · convert! NNReal.ball_zero_eq_Ico' (NNReal.mk c c_pos.le)
    simp [Real.toNNReal, c_pos.le]
  simp [c_pos]

/--
lemma `NNReal.closedBall_zero_eq_Icc'` / 引理 `NNReal.closedBall_zero_eq_Icc'`

English:
lemma NNReal.closedBall_zero_eq_Icc'
  given: (c : Real>=0)
  proof: by ext x; simp

中文:
引理 非负实数.closedBall_zero_eq_Icc'
  条件: (c : 实数>=0)
  证明: by ext x; simp
-/
lemma NNReal.closedBall_zero_eq_Icc' (c : Real>=0) :
    Metric.closedBall (0 : Real>=0) c.toReal = Set.Icc 0 c := by ext x; simp

/--
lemma `NNReal.closedBall_zero_eq_Icc` / 引理 `NNReal.closedBall_zero_eq_Icc`

English:
lemma NNReal.closedBall_zero_eq_Icc
  given: {c : Real} (c_nn : 0 <= c)
  proof: by
  convert! NNReal.closedBall_zero_eq_Icc' (NNReal.mk c c_nn)
  simp [Real.toNNReal, c_nn]

中文:
引理 非负实数.closedBall_zero_eq_Icc
  条件: {c : 实数} (c_nn : 0 <= c)
  证明: by
  convert! NNReal.closedBall_zero_eq_Icc' (NNReal.mk c c_nn)
  simp [Real.toNNReal, c_nn]

Depends on / 依赖: NNReal, NNReal.closedBall_zero_eq_Icc, NNReal.mk, Real.toNNReal, c_nn, closedBall_zero_eq_Icc, convert, toNNReal
-/
lemma NNReal.closedBall_zero_eq_Icc {c : Real} (c_nn : 0 <= c) :
    Metric.closedBall (0 : Real>=0) c = Set.Icc 0 c.toNNReal := by
  convert! NNReal.closedBall_zero_eq_Icc' (NNReal.mk c c_nn)
  simp [Real.toNNReal, c_nn]

end NNReal

namespace ULift
variable [PseudoMetricSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (ULift β)
  body: fast_instance% PseudoMetricSpace.induced ULift.down ‹_›

中文:
实例 :
  签名: 伪度量空间 (类型层提升 β)
  定义体: fast_instance% PseudoMetricSpace.induced ULift.down ‹_›

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.induced, ULift.down, fast_instance, induced
-/
instance : PseudoMetricSpace (ULift β) :=
  fast_instance% PseudoMetricSpace.induced ULift.down ‹_›

/--
lemma `dist_eq` / 引理 `dist_eq`

English:
lemma dist_eq
  given: (x y : ULift β)
  statement: dist x y = dist x.down y.down
  proof: rfl

中文:
引理 dist_eq
  条件: (x y : 类型层提升 β)
  结论: dist x y = dist x.down y.down
  证明: rfl
-/
lemma dist_eq (x y : ULift β) : dist x y = dist x.down y.down := rfl

/--
lemma `nndist_eq` / 引理 `nndist_eq`

English:
lemma nndist_eq
  given: (x y : ULift β)
  statement: nndist x y = nndist x.down y.down
  proof: rfl

中文:
引理 nndist_eq
  条件: (x y : 类型层提升 β)
  结论: nndist x y = nndist x.down y.down
  证明: rfl
-/
lemma nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down := rfl

/--
lemma `dist_up_up` / 引理 `dist_up_up`

English:
lemma dist_up_up
  given: (x y : β)
  statement: dist (ULift.up x) (ULift.up y) = dist x y
  proof: rfl

中文:
引理 dist_up_up
  条件: (x y : β)
  结论: dist (类型层提升.up x) (类型层提升.up y) = dist x y
  证明: rfl
-/
@[simp] lemma dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y := rfl

/--
lemma `nndist_up_up` / 引理 `nndist_up_up`

English:
lemma nndist_up_up
  given: (x y : β)
  statement: nndist (ULift.up x) (ULift.up y) = nndist x y
  proof: rfl

中文:
引理 nndist_up_up
  条件: (x y : β)
  结论: nndist (类型层提升.up x) (类型层提升.up y) = nndist x y
  证明: rfl
-/
@[simp] lemma nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y := rfl

end ULift

section Prod
variable [PseudoMetricSpace β]

/--
Instance `Prod.pseudoMetricSpaceMax` / 实例 `Prod.pseudoMetricSpaceMax`

English:
instance Prod.pseudoMetricSpaceMax
  signature: : PseudoMetricSpace (α × β)
  body: let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y => by positivity) fun x y => by
      simp only [ENNReal.ofReal_max, Prod.edist_eq, edist_dist]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl

中文:
实例 积类型.pseudoMetricSpaceMax
  签名: : 伪度量空间 (α × β)
  定义体: let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y => by positivity) fun x y => by
      simp only [ENNReal.ofReal_max, Prod.edist_eq, edist_dist]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl

Depends on / 依赖: ENNReal, ENNReal.ofReal_max, Prod.edist_eq, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, edist_dist, edist_eq, eventually_and, forall_and, forall_mem_image, i.replaceBornology, isBounded_iff_eventually, isBounded_image_fst_and_snd, max_le_iff, ofReal_max, replaceBornology, toPseudoMetricSpaceOfDist
-/
instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y => by positivity) fun x y => by
      simp only [ENNReal.ofReal_max, Prod.edist_eq, edist_dist]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl

/--
lemma `Prod.dist_eq` / 引理 `Prod.dist_eq`

English:
lemma Prod.dist_eq
  given: {x y : α × β}
  statement: dist x y = max (dist x.1 y.1) (dist x.2 y.2)
  proof: rfl

@[simp]

中文:
引理 积类型.dist_eq
  条件: {x y : α × β}
  结论: dist x y = 最大值 (dist x.1 y.1) (dist x.2 y.2)
  证明: rfl

@[simp]
-/
lemma Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

@[simp]
/--
lemma `dist_prod_same_left` / 引理 `dist_prod_same_left`

English:
lemma dist_prod_same_left
  given: {x : α} {y₁ y₂ : β}
  statement: dist (x, y₁) (x, y₂) = dist y₁ y₂
  proof: by
  simp [Prod.dist_eq]

@[simp]

中文:
引理 dist_prod_same_left
  条件: {x : α} {y₁ y₂ : β}
  结论: dist (x, y₁) (x, y₂) = dist y₁ y₂
  证明: by
  simp [Prod.dist_eq]

@[simp]

Depends on / 依赖: Prod.dist_eq, dist_eq
-/
lemma dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq]

@[simp]
/--
lemma `dist_prod_same_right` / 引理 `dist_prod_same_right`

English:
lemma dist_prod_same_right
  given: {x₁ x₂ : α} {y : β}
  statement: dist (x₁, y) (x₂, y) = dist x₁ x₂
  proof: by
  simp [Prod.dist_eq]

中文:
引理 dist_prod_same_right
  条件: {x₁ x₂ : α} {y : β}
  结论: dist (x₁, y) (x₂, y) = dist x₁ x₂
  证明: by
  simp [Prod.dist_eq]

Depends on / 依赖: Prod.dist_eq, dist_eq
-/
lemma dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq]

/--
lemma `ball_prod_same` / 引理 `ball_prod_same`

English:
lemma ball_prod_same
  given: (x : α) (y : β) (r : Real)
  statement: ball x r ×ˢ ball y r = ball (x, y) r
  proof: ext fun z => by simp [Prod.dist_eq]

中文:
引理 ball_prod_same
  条件: (x : α) (y : β) (r : 实数)
  结论: ball x r ×ˢ ball y r = ball (x, y) r
  证明: ext fun z => by simp [Prod.dist_eq]

Depends on / 依赖: Prod.dist_eq, dist_eq
-/
lemma ball_prod_same (x : α) (y : β) (r : Real) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]

/--
lemma `closedBall_prod_same` / 引理 `closedBall_prod_same`

English:
lemma closedBall_prod_same
  given: (x : α) (y : β) (r : Real)
  proof: ext fun z => by simp [Prod.dist_eq]

中文:
引理 closedBall_prod_same
  条件: (x : α) (y : β) (r : 实数)
  证明: ext fun z => by simp [Prod.dist_eq]

Depends on / 依赖: Prod.dist_eq, dist_eq
-/
lemma closedBall_prod_same (x : α) (y : β) (r : Real) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r := ext fun z => by simp [Prod.dist_eq]

/--
lemma `sphere_prod` / 引理 `sphere_prod`

English:
lemma sphere_prod
  given: (x : α × β) (r : Real)
  proof: by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
    all_goals rintro rfl; rfl

中文:
引理 sphere_prod
  条件: (x : α × β) (r : 实数)
  证明: by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
    all_goals rintro rfl; rfl

Depends on / 依赖: Metric, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq, Set.mem_prod, Set.mem_union, all_goals, and_comm, and_comm.trans, and_congr_left, and_congr_right, closedBall_eq_sphere_of_nonpos, closedBall_prod_same, dist_eq, le_rfl, lt_trichotomy, max_eq_iff, mem_closedBall, mem_prod, mem_sphere
-/
lemma sphere_prod (x : α × β) (r : Real) :
    sphere x r = sphere x.1 r ×ˢ closedBall x.2 r union closedBall x.1 r ×ˢ sphere x.2 r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
    all_goals rintro rfl; rfl

end Prod

/--
lemma `uniformContinuous_dist` / 引理 `uniformContinuous_dist`

English:
lemma uniformContinuous_dist
  statement: UniformContinuous fun p : α × α => dist p.1 p.2
  proof: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) <= dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ <= dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

中文:
引理 uniformContinuous_dist
  结论: 一致连续 fun p : α × α => dist p.1 p.2
  证明: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) <= dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ <= dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, add_halves, add_le_add, add_lt_add, dist_dist_dist_le, half_pos, le_max_left, le_max_right, uniformContinuous_iff
-/
lemma uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) <= dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ <= dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

/--
lemma `UniformContinuous.dist` / 引理 `UniformContinuous.dist`

English:
lemma UniformContinuous.dist
  statement: [UniformSpace β] {f g : β -> α} (hf : UniformContinuous f)
  proof: uniformContinuous_dist.comp (hf.prodMk hg)

@[continuity]

中文:
引理 一致连续.dist
  结论: [一致空间 β] {f g : β -> α} (hf : 一致连续 f)
  证明: uniformContinuous_dist.comp (hf.prodMk hg)

@[continuity]
-/
protected lemma UniformContinuous.dist [UniformSpace β] {f g : β -> α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prodMk hg)

@[continuity]
/--
lemma `continuous_dist` / 引理 `continuous_dist`

English:
lemma continuous_dist
  statement: Continuous fun p : α × α => dist p.1 p.2
  proof: uniformContinuous_dist.continuous

@[continuity, fun_prop]

中文:
引理 continuous_dist
  结论: 连续 fun p : α × α => dist p.1 p.2
  证明: uniformContinuous_dist.continuous

@[continuity, fun_prop]

Depends on / 依赖: continuous, uniformContinuous_dist, uniformContinuous_dist.continuous
-/
lemma continuous_dist : Continuous fun p : α × α => dist p.1 p.2 := uniformContinuous_dist.continuous

@[continuity, fun_prop]
/--
lemma `Continuous.dist` / 引理 `Continuous.dist`

English:
lemma Continuous.dist
  statement: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  proof: continuous_dist.comp₂ hf hg

中文:
引理 连续.dist
  结论: [拓扑空间 β] {f g : β -> α} (hf : 连续 f)
  证明: continuous_dist.comp₂ hf hg
-/
protected lemma Continuous.dist [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp₂ hf hg

/--
lemma `Filter.Tendsto.dist` / 引理 `Filter.Tendsto.dist`

English:
lemma Filter.Tendsto.dist
  statement: {f g : β -> α} {x : Filter β} {a b : α}
  proof: (continuous_dist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

中文:
引理 滤子.收敛.dist
  结论: {f g : β -> α} {x : 滤子 β} {a b : α}
  证明: (continuous_dist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
-/
protected lemma Filter.Tendsto.dist {f g : β -> α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

/--
lemma `continuous_iff_continuous_dist` / 引理 `continuous_iff_continuous_dist`

English:
lemma continuous_iff_continuous_dist
  given: [TopologicalSpace β] {f : β -> α}
  proof: ⟨fun h => h.fst'.dist h.snd', fun h =>
continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2
(h.comp (.prodMk_left _)).tendsto' _ _ dist_self _⟩

中文:
引理 continuous_iff_continuous_dist
  条件: [拓扑空间 β] {f : β -> α}
  证明: ⟨fun h => h.fst'.dist h.snd', fun h =>
continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2
(h.comp (.prodMk_left _)).tendsto' _ _ dist_self _⟩

Depends on / 依赖: continuous_iff_continuousAt, dist_self, h.comp, h.fst, h.snd, prodMk_left, tendsto, tendsto_iff_dist_tendsto_zero
-/
lemma continuous_iff_continuous_dist [TopologicalSpace β] {f : β -> α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => h.fst'.dist h.snd', fun h =>
continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2
(h.comp (.prodMk_left _)).tendsto' _ _ dist_self _⟩

/--
lemma `uniformContinuous_nndist` / 引理 `uniformContinuous_nndist`

English:
lemma uniformContinuous_nndist
  statement: UniformContinuous fun p : α × α => nndist p.1 p.2
  proof: uniformContinuous_dist.subtype_mk _

中文:
引理 uniformContinuous_nndist
  结论: 一致连续 fun p : α × α => nndist p.1 p.2
  证明: uniformContinuous_dist.subtype_mk _

Depends on / 依赖: subtype_mk, uniformContinuous_dist, uniformContinuous_dist.subtype_mk
-/
lemma uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _

/--
lemma `UniformContinuous.nndist` / 引理 `UniformContinuous.nndist`

English:
lemma UniformContinuous.nndist
  statement: [UniformSpace β] {f g : β -> α} (hf : UniformContinuous f)
  proof: uniformContinuous_nndist.comp (hf.prodMk hg)

中文:
引理 一致连续.nndist
  结论: [一致空间 β] {f g : β -> α} (hf : 一致连续 f)
  证明: uniformContinuous_nndist.comp (hf.prodMk hg)
-/
protected lemma UniformContinuous.nndist [UniformSpace β] {f g : β -> α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prodMk hg)

/--
lemma `continuous_nndist` / 引理 `continuous_nndist`

English:
lemma continuous_nndist
  statement: Continuous fun p : α × α => nndist p.1 p.2
  proof: uniformContinuous_nndist.continuous

@[fun_prop]

中文:
引理 continuous_nndist
  结论: 连续 fun p : α × α => nndist p.1 p.2
  证明: uniformContinuous_nndist.continuous

@[fun_prop]

Depends on / 依赖: continuous, uniformContinuous_nndist, uniformContinuous_nndist.continuous
-/
lemma continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.continuous

@[fun_prop]
/--
lemma `Continuous.nndist` / 引理 `Continuous.nndist`

English:
lemma Continuous.nndist
  statement: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  proof: continuous_nndist.comp₂ hf hg

中文:
引理 连续.nndist
  结论: [拓扑空间 β] {f g : β -> α} (hf : 连续 f)
  证明: continuous_nndist.comp₂ hf hg
-/
protected lemma Continuous.nndist [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp₂ hf hg

/--
lemma `Filter.Tendsto.nndist` / 引理 `Filter.Tendsto.nndist`

English:
lemma Filter.Tendsto.nndist
  statement: {f g : β -> α} {x : Filter β} {a b : α}
  proof: (continuous_nndist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

中文:
引理 滤子.收敛.nndist
  结论: {f g : β -> α} {x : 滤子 β} {a b : α}
  证明: (continuous_nndist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
-/
protected lemma Filter.Tendsto.nndist {f g : β -> α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
