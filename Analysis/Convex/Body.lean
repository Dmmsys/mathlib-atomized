/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Convex bodies

This file contains the definition of the type `ConvexBody V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`ConvexBody V` is a module over the nonnegative reals (`NNReal`) and a pseudo-metric space.
If `V` is a normed space, `ConvexBody V` is a metric space.

## TODO

- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets
- Characterise the interaction of the distance with algebraic operations, e.g.
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/

public section


open scoped Pointwise Topology NNReal

variable {V : Type*}

/--
Definition of `ConvexBody` / `ConvexBody` 的定义

English:
structure ConvexBody
  parameters: (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul Real V]
  axioms and operations (4):
    - carrier : Set V
    - convex' : Convex Real carrier
    - isCompact' : IsCompact carrier
    - nonempty' : carrier.Nonempty

中文:
结构 余nvexBody
  参数: (V : 类型) [拓扑空间 V] [加法交换幺半群 V] [标量乘法 实数 V]
  公理与运算 (4 个):
    - carrier : 集合 V
    - convex' : 凸 实数 carrier
    - isCompact' : 是紧集 carrier
    - nonempty' : carrier.非空
-/
structure ConvexBody (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul Real V] where
  /-- The **carrier set** underlying a convex body: the set of points contained in it -/
  carrier : Set V
  /-- A convex body has convex carrier set -/
  convex' : Convex Real carrier
  /-- A convex body has compact carrier set -/
  isCompact' : IsCompact carrier
  /-- A convex body has non-empty carrier set -/
  nonempty' : carrier.Nonempty

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module Real V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ConvexBody V) V
  body: ConvexBody.carrier
  coe_injective K L h := by
    cases K
    cases L
    congr

中文:
实例 :
  签名: 集合状 (余nvexBody V) V
  定义体: ConvexBody.carrier
  coe_injective K L h := by
    cases K
    cases L
    congr

Depends on / 依赖: ConvexBody, ConvexBody.carrier, carrier
-/
instance : SetLike (ConvexBody V) V where
  coe := ConvexBody.carrier
  coe_injective K L h := by
    cases K
    cases L
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ConvexBody V)
  body: .ofSetLike (ConvexBody V) V

中文:
实例 :
  签名: 偏序 (余nvexBody V)
  定义体: .ofSetLike (ConvexBody V) V

Depends on / 依赖: ConvexBody, ofSetLike
-/
instance : PartialOrder (ConvexBody V) := .ofSetLike (ConvexBody V) V

/--
theorem `convex` / 定理 `convex`

English:
theorem convex
  given: (K : ConvexBody V)
  statement: Convex Real (K : Set V)
  proof: K.convex'

中文:
定理 convex
  条件: (K : 余nvexBody V)
  结论: 凸 实数 (K : 集合 V)
  证明: K.convex'
-/
protected theorem convex (K : ConvexBody V) : Convex Real (K : Set V) :=
  K.convex'

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (K : ConvexBody V)
  statement: IsCompact (K : Set V)
  proof: K.isCompact'

中文:
定理 isCompact
  条件: (K : 余nvexBody V)
  结论: 是紧集 (K : 集合 V)
  证明: K.isCompact'
-/
protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.isCompact'

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: [T2Space V] (K : ConvexBody V)
  statement: IsClosed (K : Set V)
  proof: K.isCompact.isClosed

中文:
定理 isClosed
  条件: [T2空间 V] (K : 余nvexBody V)
  结论: 是闭集 (K : 集合 V)
  证明: K.isCompact.isClosed
-/
protected theorem isClosed [T2Space V] (K : ConvexBody V) : IsClosed (K : Set V) :=
  K.isCompact.isClosed

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (K : ConvexBody V)
  statement: (K : Set V).Nonempty
  proof: K.nonempty'

@[ext]

中文:
定理 nonempty
  条件: (K : 余nvexBody V)
  结论: (K : 集合 V).非空
  证明: K.nonempty'

@[ext]
-/
protected theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {K L : ConvexBody V} (h : (K : Set V) = L)
  statement: K = L
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {K L : 余nvexBody V} (h : (K : 集合 V) = L)
  结论: K = L
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set V) (h₁ h₂ h₃)
  statement: (mk s h₁ h₂ h₃ : Set V) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : 集合 V) (h₁ h₂ h₃)
  结论: (mk s h₁ h₂ h₃ : 集合 V) = s
  证明: rfl
-/
theorem coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s :=
  rfl

/--
theorem `zero_mem_of_symmetric` / 定理 `zero_mem_of_symmetric`

English:
theorem zero_mem_of_symmetric
  given: (K : ConvexBody V) (h_symm : forall x in K, -x in K)
  statement: 0 in K
  proof: by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1 / 2 : Real) • x + (1 / 2 : Real) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

中文:
定理 zero_mem_of_symmetric
  条件: (K : 余nvexBody V) (h_symm : 对任意 x in K, -x in K)
  结论: 0 in K
  证明: by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1 / 2 : Real) • x + (1 / 2 : Real) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

Depends on / 依赖: K.convex, K.nonempty, all_goals, convex, convex_iff_forall_pos, convex_iff_forall_pos.mp, h_symm, nonempty
-/
theorem zero_mem_of_symmetric (K : ConvexBody V) (h_symm : forall x in K, -x in K) : 0 in K := by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1 / 2 : Real) • x + (1 / 2 : Real) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

section ContinuousAdd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ConvexBody V)
  body: ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 零 (余nvexBody V)
  定义体: ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

@[simp, norm_cast]

Depends on / 依赖: Set.singleton_nonempty, convex_singleton, isCompact_singleton, singleton_nonempty
-/
instance : Zero (ConvexBody V) where
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: (↑(0 : ConvexBody V) : Set V) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: (↑(0 : 余nvexBody V) : 集合 V) = 0
  证明: rfl
-/
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ConvexBody V)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (余nvexBody V)
  定义体: ⟨0⟩
-/
instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

variable [ContinuousAdd V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (ConvexBody V)
  body: ⟨K + L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩

中文:
实例 :
  签名: 加法 (余nvexBody V)
  定义体: ⟨K + L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩

Depends on / 依赖: K.convex.add, K.isCompact.add, K.nonempty.add, L.convex, L.isCompact, L.nonempty, convex, isCompact, nonempty
-/
instance : Add (ConvexBody V) where
  add K L :=
    ⟨K + L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (ConvexBody V)
  body: nsmulRec

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 自然数 (余nvexBody V)
  定义体: nsmulRec

@[simp, norm_cast]

Depends on / 依赖: nsmulRec
-/
instance : SMul Nat (ConvexBody V) where
  smul := nsmulRec

@[simp, norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  statement: forall (n : Nat) (K : ConvexBody V), ↑(n • K) = n • (K : Set V)

中文:
定理 coe_nsmul
  结论: 对任意 (n : 自然数) (K : 余nvexBody V), ↑(n • K) = n • (K : 集合 V)
-/
theorem coe_nsmul : forall (n : Nat) (K : ConvexBody V), ↑(n • K) = n • (K : Set V)
  | 0, _ => rfl
  | (n + 1), K => congr_arg₂ (Set.image2 (· + ·)) (coe_nsmul n K) rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (ConvexBody V)
  body: SetLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

@[simp, norm_cast]

中文:
实例 :
  签名: 加法幺半群 (余nvexBody V)
  定义体: SetLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective.addMonoid, addMonoid, coe_injective, coe_nsmul
-/
noncomputable instance : AddMonoid (ConvexBody V) :=
  SetLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (K L : ConvexBody V)
  statement: (↑(K + L) : Set V) = (K : Set V) + L
  proof: rfl

中文:
定理 coe_add
  条件: (K L : 余nvexBody V)
  结论: (↑(K + L) : 集合 V) = (K : 集合 V) + L
  证明: rfl
-/
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (ConvexBody V)
  body: SetLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

中文:
实例 :
  签名: 加法交换幺半群 (余nvexBody V)
  定义体: SetLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

Depends on / 依赖: SetLike, SetLike.coe_injective.addCommMonoid, addCommMonoid, coe_injective, coe_nsmul
-/
noncomputable instance : AddCommMonoid (ConvexBody V) :=
  SetLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_nsmul _ _

end ContinuousAdd

variable [ContinuousSMul Real V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Real (ConvexBody V)
  body: ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 实数 (余nvexBody V)
  定义体: ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp, norm_cast]

Depends on / 依赖: K.convex.smul, K.isCompact.smul, K.nonempty.smul_set, convex, isCompact, nonempty, smul_set
-/
instance : SMul Real (ConvexBody V) where
  smul c K := ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : Real) (K : ConvexBody V)
  statement: (↑(c • K) : Set V) = c • (K : Set V)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_smul
  条件: (c : 实数) (K : 余nvexBody V)
  结论: (↑(c • K) : 集合 V) = c • (K : 集合 V)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_smul (c : Real) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul'` / 定理 `coe_smul'`

English:
theorem coe_smul'
  given: (c : Real>=0) (K : ConvexBody V)
  statement: (↑(c • K) : Set V) = c • (K : Set V)
  proof: rfl

中文:
定理 coe_smul'
  条件: (c : 实数>=0) (K : 余nvexBody V)
  结论: (↑(c • K) : 集合 V) = c • (K : 集合 V)
  证明: rfl
-/
theorem coe_smul' (c : Real>=0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl

/--
theorem `smul_le_of_le` / 定理 `smul_le_of_le`

English:
theorem smul_le_of_le
  given: (K : ConvexBody V) (h_zero : 0 in K) {a b : Real>=0} (h : a <= b)
  proof: by
  rw [← SetLike.coe_subset_coe]; rw [coe_smul']; rw [coe_smul']
  obtain rfl | ha := eq_zero_or_pos a
  · rw [Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_i

中文:
定理 smul_le_of_le
  条件: (K : 余nvexBody V) (h_zero : 0 in K) {a b : 实数>=0} (h : a <= b)
  证明: by
  rw [← SetLike.coe_subset_coe]; rw [coe_smul']; rw [coe_smul']
  obtain rfl | ha := eq_zero_or_pos a
  · rw [Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_i

Depends on / 依赖: Convex, Convex.mem_smul_of_zero_mem, K.convex, K.nonempty, Set.mem_inv_smul_set_iff, Set.mem_smul_set.mp, Set.mem_smul_set.mpr, Set.zero_smul_set, Set.zero_subset, SetLike, SetLike.coe_subset_coe, coe_smul, coe_subset_coe, convex, eq_zero_or_pos, h_zero, ha.ne, mem_smul_of_zero_mem, mem_smul_set, mul_one
-/
theorem smul_le_of_le (K : ConvexBody V) (h_zero : 0 in K) {a b : Real>=0} (h : a <= b) :
    a • K <= b • K := by
  rw [← SetLike.coe_subset_coe]; rw [coe_smul']; rw [coe_smul']
  obtain rfl | ha := eq_zero_or_pos a
  · rw [Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_inv_smul_set_iff₀ ha.ne']; rw [smul_smul]
    refine Convex.mem_smul_of_zero_mem K.convex h_zero hy (?_ : 1 <= a⁻¹ * b)
    rwa [le_inv_mul_iff₀ ha, mul_one]

variable [ContinuousAdd V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction Real (ConvexBody V)
  body: SetLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

中文:
实例 :
  签名: 分配乘法作用 实数 (余nvexBody V)
  定义体: SetLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

Depends on / 依赖: SetLike, SetLike.coe_injective.distribMulAction, coe_add, coe_injective, coe_smul, coe_zero, distribMulAction
-/
noncomputable instance : DistribMulAction Real (ConvexBody V) :=
  SetLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Real>=0 (ConvexBody V)
  body: SetLike.ext' Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
zero_smul K := SetLike.ext' Set.zero_smul_set K.nonempty

中文:
实例 :
  签名: 模 实数>=0 (余nvexBody V)
  定义体: SetLike.ext' Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
zero_smul K := SetLike.ext' Set.zero_smul_set K.nonempty

Depends on / 依赖: Convex, Convex.add_smul, K.convex, SetLike, SetLike.ext, add_smul, c.coe_nonneg, coe_nonneg, convex, d.coe_nonneg
-/
noncomputable instance : Module Real>=0 (ConvexBody V) where
add_smul c d K := SetLike.ext' Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
zero_smul K := SetLike.ext' Set.zero_smul_set K.nonempty

end TVS

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup V] [NormedSpace Real V] (K L : ConvexBody V)

/--
theorem `isBounded` / 定理 `isBounded`

English:
theorem isBounded
  statement: Bornology.IsBounded (K : Set V)
  proof: K.isCompact.isBounded

中文:
定理 isBounded
  结论: 有界结构.IsBounded (K : 集合 V)
  证明: K.isCompact.isBounded
-/
protected theorem isBounded : Bornology.IsBounded (K : Set V) :=
  K.isCompact.isBounded

/--
theorem `hausdorffEDist_ne_top` / 定理 `hausdorffEDist_ne_top`

English:
theorem hausdorffEDist_ne_top
  given: {K L : ConvexBody V}
  statement: Metric.hausdorffEDist (K : Set V) L != ⊤
  proof: by
  apply_rules [Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top := hausdorffEDist_ne_top

中文:
定理 hausdorffEDist_ne_top
  条件: {K L : 余nvexBody V}
  结论: Metric.hausdorffEDist (K : 集合 V) L != ⊤
  证明: by
  apply_rules [Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top := hausdorffEDist_ne_top

Depends on / 依赖: ConvexBody, ConvexBody.isBounded, ConvexBody.nonempty, Metric, Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, apply_rules, hausdorffEDist_ne_top_of_nonempty_of_bounded, isBounded, nonempty
-/
theorem hausdorffEDist_ne_top {K L : ConvexBody V} : Metric.hausdorffEDist (K : Set V) L != ⊤ := by
  apply_rules [Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top := hausdorffEDist_ne_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (ConvexBody V)
  body: Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle _ _ _ := Metric.hausdorffDist_triangle hausdorffEDist_ne_top

@[simp, norm_cast]

中文:
实例 :
  签名: 伪度量空间 (余nvexBody V)
  定义体: Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle _ _ _ := Metric.hausdorffDist_triangle hausdorffEDist_ne_top

@[simp, norm_cast]

Depends on / 依赖: Metric, Metric.hausdorffDist, hausdorffDist
-/
noncomputable instance : PseudoMetricSpace (ConvexBody V) where
  dist K L := Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle _ _ _ := Metric.hausdorffDist_triangle hausdorffEDist_ne_top

@[simp, norm_cast]
/--
theorem `hausdorffDist_coe` / 定理 `hausdorffDist_coe`

English:
theorem hausdorffDist_coe
  statement: Metric.hausdorffDist (K : Set V) L = dist K L
  proof: rfl

@[simp, norm_cast]

中文:
定理 hausdorffDist_coe
  结论: Metric.hausdorffDist (K : 集合 V) L = dist K L
  证明: rfl

@[simp, norm_cast]
-/
theorem hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L :=
  rfl

@[simp, norm_cast]
/--
theorem `hausdorffEDist_coe` / 定理 `hausdorffEDist_coe`

English:
theorem hausdorffEDist_coe
  statement: Metric.hausdorffEDist (K : Set V) L = edist K L
  proof: by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEDist_ne_top).symm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_coe := hausdorffEDist_coe

中文:
定理 hausdorffEDist_coe
  结论: Metric.hausdorffEDist (K : 集合 V) L = edist K L
  证明: by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEDist_ne_top).symm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_coe := hausdorffEDist_coe

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, edist_dist, hausdorffEDist_ne_top, ofReal_toReal
-/
theorem hausdorffEDist_coe : Metric.hausdorffEDist (K : Set V) L = edist K L := by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEDist_ne_top).symm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_coe := hausdorffEDist_coe

open Filter

/--
theorem `iInter_smul_eq_self` / 定理 `iInter_smul_eq_self`

English:
theorem iInter_smul_eq_self
  statement: [T2Space V] {u : Nat -> Real>=0} (K : ConvexBody V) (h_zero : 0 in K)
  proof: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨C, hC_pos, hC_bdd⟩ := K.isBounded.exists_pos_norm_le
    rw [← K.isClosed.closure_eq]; rw [SeminormedAddCommGroup.mem_closure_iff]
    rw [← NNReal.tendsto_coe]; rw [NormedAddCommGroup.tendsto_atTop] at hu
    intro ε hε
    obtain ⟨n, hn⟩ :

中文:
定理 i整数er_smul_eq_self
  结论: [T2空间 V] {u : 自然数 -> 实数>=0} (K : 余nvexBody V) (h_zero : 0 in K)
  证明: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨C, hC_pos, hC_bdd⟩ := K.isBounded.exists_pos_norm_le
    rw [← K.isClosed.closure_eq]; rw [SeminormedAddCommGroup.mem_closure_iff]
    rw [← NNReal.tendsto_coe]; rw [NormedAddCommGroup.tendsto_atTop] at hu
    intro ε hε
    obtain ⟨n, hn⟩ :

Depends on / 依赖: K.isBounded.exists_pos_norm_le, K.isClosed.closure_eq, NNReal, NNReal.tendsto_coe, NormedAddCommGroup, NormedAddCommGroup.tendsto_atTop, SeminormedAddCommGroup, SeminormedAddCommGroup.mem_closure_iff, Set.mem_iInter.mp, Set.mem_smul_set.mp, add_smul, add_sub_can, closure_eq, div_pos, exists_pos_norm_le, hC_bdd, hC_pos, isBounded, isClosed, mem_closure_iff
-/
theorem iInter_smul_eq_self [T2Space V] {u : Nat -> Real>=0} (K : ConvexBody V) (h_zero : 0 in K)
    (hu : Tendsto u atTop (𝓝 0)) :
    ⋂ n : Nat, (1 + (u n : Real)) • (K : Set V) = K := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨C, hC_pos, hC_bdd⟩ := K.isBounded.exists_pos_norm_le
    rw [← K.isClosed.closure_eq]; rw [SeminormedAddCommGroup.mem_closure_iff]
    rw [← NNReal.tendsto_coe]; rw [NormedAddCommGroup.tendsto_atTop] at hu
    intro ε hε
    obtain ⟨n, hn⟩ := hu (ε / C) (div_pos hε hC_pos)
    obtain ⟨y, hyK, rfl⟩ := Set.mem_smul_set.mp (Set.mem_iInter.mp h n)
    refine ⟨y, hyK, ?_⟩
    rw [show (1 + u n : Real) • y - y = (u n : Real) • y by rw [add_smul]; rw [one_smul]; rw [add_sub_cancel_left],
      norm_smul, Real.norm_eq_abs]
    specialize hn n le_rfl
    rw [lt_div_iff₀' hC_pos]; rw [mul_comm]; rw [NNReal.coe_zero]; rw [sub_zero]; rw [Real.norm_eq_abs] at hn
    refine lt_of_le_of_lt ?_ hn
    gcongr; exact hC_bdd _ hyK
  · refine Set.mem_iInter.mpr (fun n => Convex.mem_smul_of_zero_mem K.convex h_zero h ?_)
    exact le_add_of_nonneg_right (by positivity)

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup V] [NormedSpace Real V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace (ConvexBody V)
  body: ConvexBody.ext
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEDist_ne_top).1 hd

中文:
实例 :
  签名: 度量空间 (余nvexBody V)
  定义体: ConvexBody.ext
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEDist_ne_top).1 hd

Depends on / 依赖: ConvexBody, ConvexBody.ext
-/
noncomputable instance : MetricSpace (ConvexBody V) where
eq_of_dist_eq_zero {K L} hd := ConvexBody.ext
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEDist_ne_top).1 hd

end NormedAddCommGroup

end ConvexBody
