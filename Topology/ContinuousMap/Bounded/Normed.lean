/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Inheritance of normed algebraic structures by bounded continuous functions

For various types of normed algebraic structures `β`, we show in this file that the space of
bounded continuous functions from `α` to `β` inherits the same normed structure, by using
pointwise operations and checking that they are compatible with the uniform distance.
-/

@[expose] public section

assert_not_exists CStarRing

noncomputable section

open NNReal Set Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

section NormedAddCommGroup

variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable (f g : α ->ᵇ β) {x : α} {C : Real}

/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm (α ->ᵇ β)
  body: ⟨(dist · 0)⟩

中文:
实例 instNorm
  签名: : 范数 (α ->ᵇ β)
  定义体: ⟨(dist · 0)⟩
-/
instance instNorm : Norm (α ->ᵇ β) := ⟨(dist · 0)⟩

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  statement: ‖f‖ = dist f 0
  proof: rfl

中文:
定理 norm_def
  结论: ‖f‖ = dist f 0
  证明: rfl
-/
theorem norm_def : ‖f‖ = dist f 0 := rfl

/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: (f : α ->ᵇ β)
  statement: ‖f‖ = sInf { C : Real | 0 <= C ∧ forall x : α, ‖f x‖ <= C }
  proof: by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

中文:
定理 norm_eq
  条件: (f : α ->ᵇ β)
  结论: ‖f‖ = sInf { C : 实数 | 0 <= C ∧ 对任意 x : α, ‖f x‖ <= C }
  证明: by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.dist_eq, dist_eq, norm_def
-/
theorem norm_eq (f : α ->ᵇ β) : ‖f‖ = sInf { C : Real | 0 <= C ∧ forall x : α, ‖f x‖ <= C } := by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

/--
theorem `norm_eq_of_nonempty` / 定理 `norm_eq_of_nonempty`

English:
theorem norm_eq_of_nonempty
  given: [h : Nonempty α]
  statement: ‖f‖ = sInf { C : Real | forall x : α, ‖f x‖ <= C }
  proof: by
  obtain ⟨a⟩ := h
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_trans (norm_nonneg (f a)) (h' a)

@[simp]

中文:
定理 norm_eq_of_nonempty
  条件: [h : 非空 α]
  结论: ‖f‖ = sInf { C : 实数 | 对任意 x : α, ‖f x‖ <= C }
  证明: by
  obtain ⟨a⟩ := h
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_trans (norm_nonneg (f a)) (h' a)

@[simp]

Depends on / 依赖: and_iff_right_iff_imp, le_trans, norm_eq, norm_nonneg
-/
theorem norm_eq_of_nonempty [h : Nonempty α] : ‖f‖ = sInf { C : Real | forall x : α, ‖f x‖ <= C } := by
  obtain ⟨a⟩ := h
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_trans (norm_nonneg (f a)) (h' a)

@[simp]
/--
theorem `norm_eq_zero_of_empty` / 定理 `norm_eq_zero_of_empty`

English:
theorem norm_eq_zero_of_empty
  given: [IsEmpty α]
  statement: ‖f‖ = 0
  proof: dist_zero_of_empty

中文:
定理 norm_eq_zero_of_empty
  条件: [是空 α]
  结论: ‖f‖ = 0
  证明: dist_zero_of_empty

Depends on / 依赖: dist_zero_of_empty
-/
theorem norm_eq_zero_of_empty [IsEmpty α] : ‖f‖ = 0 :=
  dist_zero_of_empty

/--
theorem `norm_coe_le_norm` / 定理 `norm_coe_le_norm`

English:
theorem norm_coe_le_norm
  given: (x : α)
  statement: ‖f x‖ <= ‖f‖
  proof: calc
    ‖f x‖ = dist (f x) ((0 : α ->ᵇ β) x) := by simp [dist_zero_right]
    _ <= ‖f‖ := dist_coe_le_dist _

中文:
定理 norm_coe_le_norm
  条件: (x : α)
  结论: ‖f x‖ <= ‖f‖
  证明: calc
    ‖f x‖ = dist (f x) ((0 : α ->ᵇ β) x) := by simp [dist_zero_right]
    _ <= ‖f‖ := dist_coe_le_dist _

Depends on / 依赖: dist_coe_le_dist, dist_zero_right
-/
theorem norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖ :=
  calc
    ‖f x‖ = dist (f x) ((0 : α ->ᵇ β) x) := by simp [dist_zero_right]
    _ <= ‖f‖ := dist_coe_le_dist _

/--
lemma `neg_norm_le_apply` / 引理 `neg_norm_le_apply`

English:
lemma neg_norm_le_apply
  given: (f : α ->ᵇ Real) (x : α)
  proof: (abs_le.mp (norm_coe_le_norm f x)).1

中文:
引理 neg_norm_le_apply
  条件: (f : α ->ᵇ 实数) (x : α)
  证明: (abs_le.mp (norm_coe_le_norm f x)).1

Depends on / 依赖: abs_le, abs_le.mp, norm_coe_le_norm
-/
lemma neg_norm_le_apply (f : α ->ᵇ Real) (x : α) :
    -‖f‖ <= f x := (abs_le.mp (norm_coe_le_norm f x)).1

/--
lemma `apply_le_norm` / 引理 `apply_le_norm`

English:
lemma apply_le_norm
  given: (f : α ->ᵇ Real) (x : α)
  proof: (abs_le.mp (norm_coe_le_norm f x)).2

中文:
引理 apply_le_norm
  条件: (f : α ->ᵇ 实数) (x : α)
  证明: (abs_le.mp (norm_coe_le_norm f x)).2

Depends on / 依赖: abs_le, abs_le.mp, norm_coe_le_norm
-/
lemma apply_le_norm (f : α ->ᵇ Real) (x : α) :
    f x <= ‖f‖ := (abs_le.mp (norm_coe_le_norm f x)).2

/--
theorem `dist_le_two_norm'` / 定理 `dist_le_two_norm'`

English:
theorem dist_le_two_norm'
  given: {f : γ -> β} {C : Real} (hC : forall x, ‖f x‖ <= C) (x y : γ)
  proof: calc
    dist (f x) (f y) <= ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ <= C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm

中文:
定理 dist_le_two_norm'
  条件: {f : γ -> β} {C : 实数} (hC : 对任意 x, ‖f x‖ <= C) (x y : γ)
  证明: calc
    dist (f x) (f y) <= ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ <= C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm

Depends on / 依赖: add_le_add, dist_le_norm_add_norm, two_mul
-/
theorem dist_le_two_norm' {f : γ -> β} {C : Real} (hC : forall x, ‖f x‖ <= C) (x y : γ) :
    dist (f x) (f y) <= 2 * C :=
  calc
    dist (f x) (f y) <= ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ <= C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm

/--
theorem `dist_le_two_norm` / 定理 `dist_le_two_norm`

English:
theorem dist_le_two_norm
  given: (x y : α)
  statement: dist (f x) (f y) <= 2 * ‖f‖
  proof: dist_le_two_norm' f.norm_coe_le_norm x y

中文:
定理 dist_le_two_norm
  条件: (x y : α)
  结论: dist (f x) (f y) <= 2 * ‖f‖
  证明: dist_le_two_norm' f.norm_coe_le_norm x y

Depends on / 依赖: dist_le_two_norm, f.norm_coe_le_norm, norm_coe_le_norm
-/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) <= 2 * ‖f‖ :=
  dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/--
theorem `norm_le` / 定理 `norm_le`

English:
theorem norm_le
  given: (C0 : (0 : Real) <= C)
  statement: ‖f‖ <= C ↔ forall x : α, ‖f x‖ <= C
  proof: by
  simpa using! @dist_le _ _ _ _ f 0 _ C0

中文:
定理 norm_le
  条件: (C0 : (0 : 实数) <= C)
  结论: ‖f‖ <= C ↔ 对任意 x : α, ‖f x‖ <= C
  证明: by
  simpa using! @dist_le _ _ _ _ f 0 _ C0

Depends on / 依赖: dist_le
-/
theorem norm_le (C0 : (0 : Real) <= C) : ‖f‖ <= C ↔ forall x : α, ‖f x‖ <= C := by
  simpa using! @dist_le _ _ _ _ f 0 _ C0

/--
theorem `norm_le_of_nonempty` / 定理 `norm_le_of_nonempty`

English:
theorem norm_le_of_nonempty
  given: [Nonempty α] {f : α ->ᵇ β} {M : Real}
  statement: ‖f‖ <= M ↔ forall x, ‖f x‖ <= M
  proof: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty

中文:
定理 norm_le_of_nonempty
  条件: [非空 α] {f : α ->ᵇ β} {M : 实数}
  结论: ‖f‖ <= M ↔ 对任意 x, ‖f x‖ <= M
  证明: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty

Depends on / 依赖: dist_le_iff_of_nonempty, dist_zero_right, norm_def, simp_rw
-/
theorem norm_le_of_nonempty [Nonempty α] {f : α ->ᵇ β} {M : Real} : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty

/--
theorem `norm_lt_iff_of_compact` / 定理 `norm_lt_iff_of_compact`

English:
theorem norm_lt_iff_of_compact
  given: [CompactSpace α] {f : α ->ᵇ β} {M : Real} (M0 : 0 < M)
  proof: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0

中文:
定理 norm_lt_iff_of_compact
  条件: [紧空间 α] {f : α ->ᵇ β} {M : 实数} (M0 : 0 < M)
  证明: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0

Depends on / 依赖: dist_lt_iff_of_compact, dist_zero_right, norm_def, simp_rw
-/
theorem norm_lt_iff_of_compact [CompactSpace α] {f : α ->ᵇ β} {M : Real} (M0 : 0 < M) :
    ‖f‖ < M ↔ forall x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0

/--
theorem `norm_lt_iff_of_nonempty_compact` / 定理 `norm_lt_iff_of_nonempty_compact`

English:
theorem norm_lt_iff_of_nonempty_compact
  given: [Nonempty α] [CompactSpace α] {f : α ->ᵇ β} {M : Real}
  proof: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

中文:
定理 norm_lt_iff_of_nonempty_compact
  条件: [非空 α] [紧空间 α] {f : α ->ᵇ β} {M : 实数}
  证明: by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

Depends on / 依赖: dist_lt_iff_of_nonempty_compact, dist_zero_right, norm_def, simp_rw
-/
theorem norm_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] {f : α ->ᵇ β} {M : Real} :
    ‖f‖ < M ↔ forall x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

variable (f)

/--
theorem `norm_const_le` / 定理 `norm_const_le`

English:
theorem norm_const_le
  given: (b : β)
  statement: ‖const α b‖ <= ‖b‖
  proof: (norm_le (norm_nonneg b)).2 fun _ => le_rfl

@[simp]

中文:
定理 norm_const_le
  条件: (b : β)
  结论: ‖const α b‖ <= ‖b‖
  证明: (norm_le (norm_nonneg b)).2 fun _ => le_rfl

@[simp]

Depends on / 依赖: le_rfl, norm_le, norm_nonneg
-/
theorem norm_const_le (b : β) : ‖const α b‖ <= ‖b‖ :=
  (norm_le (norm_nonneg b)).2 fun _ => le_rfl

@[simp]
/--
theorem `norm_const_eq` / 定理 `norm_const_eq`

English:
theorem norm_const_eq
  given: [h : Nonempty α] (b : β)
  statement: ‖const α b‖ = ‖b‖
  proof: le_antisymm (norm_const_le b) h.elim fun x => (const α b).norm_coe_le_norm x

中文:
定理 norm_const_eq
  条件: [h : 非空 α] (b : β)
  结论: ‖const α b‖ = ‖b‖
  证明: le_antisymm (norm_const_le b) h.elim fun x => (const α b).norm_coe_le_norm x

Depends on / 依赖: h.elim, le_antisymm, norm_coe_le_norm, norm_const_le
-/
theorem norm_const_eq [h : Nonempty α] (b : β) : ‖const α b‖ = ‖b‖ :=
le_antisymm (norm_const_le b) h.elim fun x => (const α b).norm_coe_le_norm x

/--
Definition of `ofNormedAddCommGroup` / `ofNormedAddCommGroup` 的定义

English:
definition ofNormedAddCommGroup
  signature: {α : Type u} {β : Type v} [TopologicalSpace α] [SeminormedAddCommGroup β]
  body: ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]

中文:
定义 ofNormedAddCommGroup
  签名: {α : 类型u} {β : 类型v} [拓扑空间 α] [SeminormedAddComm群 β]
  定义体: ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]

Depends on / 依赖: dist_le_two_norm
-/
def ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [SeminormedAddCommGroup β]
    (f : α -> β) (Hf : Continuous f) (C : Real) (H : forall x, ‖f x‖ <= C) : α ->ᵇ β :=
  ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]
/--
theorem `coe_ofNormedAddCommGroup` / 定理 `coe_ofNormedAddCommGroup`

English:
theorem coe_ofNormedAddCommGroup
  statement: {α : Type u} {β : Type v} [TopologicalSpace α]
  proof: rfl

中文:
定理 coe_ofNormedAddCommGroup
  结论: {α : 类型u} {β : 类型v} [拓扑空间 α]
  证明: rfl
-/
theorem coe_ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α]
    [SeminormedAddCommGroup β] (f : α -> β) (Hf : Continuous f) (C : Real) (H : forall x, ‖f x‖ <= C) :
    (ofNormedAddCommGroup f Hf C H : α -> β) = f := rfl

/--
theorem `norm_ofNormedAddCommGroup_le` / 定理 `norm_ofNormedAddCommGroup_le`

English:
theorem norm_ofNormedAddCommGroup_le
  statement: {f : α -> β} (hfc : Continuous f) {C : Real} (hC : 0 <= C)
  proof: (norm_le hC).2 hfC

中文:
定理 norm_ofNormedAddCommGroup_le
  结论: {f : α -> β} (hfc : 连续 f) {C : 实数} (hC : 0 <= C)
  证明: (norm_le hC).2 hfC

Depends on / 依赖: norm_le
-/
theorem norm_ofNormedAddCommGroup_le {f : α -> β} (hfc : Continuous f) {C : Real} (hC : 0 <= C)
    (hfC : forall x, ‖f x‖ <= C) : ‖ofNormedAddCommGroup f hfc C hfC‖ <= C :=
  (norm_le hC).2 hfC

/--
Definition of `ofNormedAddCommGroupDiscrete` / `ofNormedAddCommGroupDiscrete` 的定义

English:
definition ofNormedAddCommGroupDiscrete
  signature: {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α]
  body: ofNormedAddCommGroup f continuous_of_discreteTopology C H

@[simp]

中文:
定义 ofNormedAddCommGroupDiscrete
  签名: {α : 类型u} {β : 类型v} [拓扑空间 α] [离散拓扑 α]
  定义体: ofNormedAddCommGroup f continuous_of_discreteTopology C H

@[simp]

Depends on / 依赖: continuous_of_discreteTopology, ofNormedAddCommGroup
-/
def ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α]
    [SeminormedAddCommGroup β] (f : α -> β) (C : Real) (H : forall x, norm (f x) <= C) : α ->ᵇ β :=
  ofNormedAddCommGroup f continuous_of_discreteTopology C H

@[simp]
/--
theorem `coe_ofNormedAddCommGroupDiscrete` / 定理 `coe_ofNormedAddCommGroupDiscrete`

English:
theorem coe_ofNormedAddCommGroupDiscrete
  statement: {α : Type u} {β : Type v} [TopologicalSpace α]
  proof: rfl

中文:
定理 coe_ofNormedAddCommGroupDiscrete
  结论: {α : 类型u} {β : 类型v} [拓扑空间 α]
  证明: rfl
-/
theorem coe_ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α]
    [DiscreteTopology α] [SeminormedAddCommGroup β] (f : α -> β) (C : Real) (H : forall x, ‖f x‖ <= C) :
    (ofNormedAddCommGroupDiscrete f C H : α -> β) = f := rfl

/--
Definition of `normComp` / `normComp` 的定义

English:
definition normComp
  signature: : α ->ᵇ Real
  body: f.comp norm lipschitzWith_one_norm

@[simp]

中文:
定义 normComp
  签名: : α ->ᵇ 实数
  定义体: f.comp norm lipschitzWith_one_norm

@[simp]

Depends on / 依赖: f.comp, lipschitzWith_one_norm
-/
def normComp : α ->ᵇ Real :=
  f.comp norm lipschitzWith_one_norm

@[simp]
/--
theorem `coe_normComp` / 定理 `coe_normComp`

English:
theorem coe_normComp
  statement: (f.normComp : α -> Real) = norm ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_normComp
  结论: (f.normComp : α -> 实数) = norm ∘ f
  证明: rfl

@[simp]
-/
theorem coe_normComp : (f.normComp : α -> Real) = norm ∘ f := rfl

@[simp]
/--
theorem `norm_normComp` / 定理 `norm_normComp`

English:
theorem norm_normComp
  statement: ‖f.normComp‖ = ‖f‖
  proof: by
  simp only [norm_eq, coe_normComp, norm_norm, Function.comp]

中文:
定理 norm_normComp
  结论: ‖f.normComp‖ = ‖f‖
  证明: by
  simp only [norm_eq, coe_normComp, norm_norm, Function.comp]

Depends on / 依赖: Function, Function.comp, coe_normComp, norm_eq, norm_norm
-/
theorem norm_normComp : ‖f.normComp‖ = ‖f‖ := by
  simp only [norm_eq, coe_normComp, norm_norm, Function.comp]

/--
theorem `bddAbove_range_norm_comp` / 定理 `bddAbove_range_norm_comp`

English:
theorem bddAbove_range_norm_comp
  statement: BddAbove Set.range norm ∘ f
  proof: (@isBounded_range _ _ _ _ f.normComp).bddAbove

中文:
定理 bddAbove_range_norm_comp
  结论: BddAbove 集合.range norm ∘ f
  证明: (@isBounded_range _ _ _ _ f.normComp).bddAbove

Depends on / 依赖: bddAbove, f.normComp, isBounded_range, normComp
-/
theorem bddAbove_range_norm_comp : BddAbove Set.range norm ∘ f :=
  (@isBounded_range _ _ _ _ f.normComp).bddAbove

/--
theorem `norm_eq_iSup_norm` / 定理 `norm_eq_iSup_norm`

English:
theorem norm_eq_iSup_norm
  statement: ‖f‖ = ⨆ x : α, ‖f x‖
  proof: by
  simp_rw [norm_def, dist_eq_iSup, coe_zero, Pi.zero_apply, dist_zero_right]

中文:
定理 norm_eq_iSup_norm
  结论: ‖f‖ = ⨆ x : α, ‖f x‖
  证明: by
  simp_rw [norm_def, dist_eq_iSup, coe_zero, Pi.zero_apply, dist_zero_right]

Depends on / 依赖: Pi.zero_apply, coe_zero, dist_eq_iSup, dist_zero_right, norm_def, simp_rw, zero_apply
-/
theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ := by
  simp_rw [norm_def, dist_eq_iSup, coe_zero, Pi.zero_apply, dist_zero_right]

/--
Instance `instNormOneClass` / 实例 `instNormOneClass`

English:
instance instNormOneClass
  signature: [Nonempty α] [One β] [NormOneClass β]
  body: by simp only [norm_eq_iSup_norm, coe_one, Pi.one_apply, norm_one, ciSup_const]

中文:
实例 instNormOneClass
  签名: [非空 α] [幺 β] [NormOne类 β]
  定义体: by simp only [norm_eq_iSup_norm, coe_one, Pi.one_apply, norm_one, ciSup_const]

Depends on / 依赖: Pi.one_apply, ciSup_const, coe_one, norm_eq_iSup_norm, norm_one, one_apply
-/
instance instNormOneClass [Nonempty α] [One β] [NormOneClass β] : NormOneClass (α ->ᵇ β) where
  norm_one := by simp only [norm_eq_iSup_norm, coe_one, Pi.one_apply, norm_one, ciSup_const]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (α ->ᵇ β)
  body: ⟨fun f =>
    ofNormedAddCommGroup (-f) f.continuous.neg ‖f‖ fun x =>
      norm_neg ((⇑f) x) ▸ f.norm_coe_le_norm x⟩

@[simp]

中文:
实例 :
  签名: 取负 (α ->ᵇ β)
  定义体: ⟨fun f =>
    ofNormedAddCommGroup (-f) f.continuous.neg ‖f‖ fun x =>
      norm_neg ((⇑f) x) ▸ f.norm_coe_le_norm x⟩

@[simp]

Depends on / 依赖: continuous, f.continuous.neg, f.norm_coe_le_norm, norm_coe_le_norm, norm_neg, ofNormedAddCommGroup
-/
instance : Neg (α ->ᵇ β) :=
  ⟨fun f =>
    ofNormedAddCommGroup (-f) f.continuous.neg ‖f‖ fun x =>
      norm_neg ((⇑f) x) ▸ f.norm_coe_le_norm x⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ⇑(-f) = -f
  proof: rfl

中文:
定理 coe_neg
  结论: ⇑(-f) = -f
  证明: rfl
-/
theorem coe_neg : ⇑(-f) = -f := rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-f) x = -f x
  proof: rfl

@[simp]

中文:
定理 neg_apply
  结论: (-f) x = -f x
  证明: rfl

@[simp]
-/
theorem neg_apply : (-f) x = -f x := rfl

@[simp]
/--
theorem `mkOfCompact_neg` / 定理 `mkOfCompact_neg`

English:
theorem mkOfCompact_neg
  given: [CompactSpace α] (f : C(α, β))
  statement: mkOfCompact (-f) = -mkOfCompact f
  proof: rfl

@[simp]

中文:
定理 mkOfCompact_neg
  条件: [紧空间 α] (f : C(α, β))
  结论: mkOfCompact (-f) = -mkOfCompact f
  证明: rfl

@[simp]
-/
theorem mkOfCompact_neg [CompactSpace α] (f : C(α, β)) : mkOfCompact (-f) = -mkOfCompact f := rfl

@[simp]
/--
theorem `mkOfCompact_sub` / 定理 `mkOfCompact_sub`

English:
theorem mkOfCompact_sub
  given: [CompactSpace α] (f g : C(α, β))
  proof: rfl

@[simp]

中文:
定理 mkOfCompact_sub
  条件: [紧空间 α] (f g : C(α, β))
  证明: rfl

@[simp]
-/
theorem mkOfCompact_sub [CompactSpace α] (f g : C(α, β)) :
    mkOfCompact (f - g) = mkOfCompact f - mkOfCompact g := rfl

@[simp]
/--
theorem `coe_zsmulRec` / 定理 `coe_zsmulRec`

English:
theorem coe_zsmulRec
  statement: forall z, ⇑(zsmulRec (· • ·) z f) = z • ⇑f

中文:
定理 coe_zsmulRec
  结论: 对任意 z, ⇑(zsmulRec (· • ·) z f) = z • ⇑f
-/
theorem coe_zsmulRec : forall z, ⇑(zsmulRec (· • ·) z f) = z • ⇑f
  | Int.ofNat n => by rw [zsmulRec, Int.ofNat_eq_natCast, coe_nsmul, natCast_zsmul]
  | Int.negSucc n => by rw [zsmulRec, negSucc_zsmul, coe_neg, coe_nsmul]

/--
Instance `instSMulInt` / 实例 `instSMulInt`

English:
instance instSMulInt
  signature: : SMul Int (α ->ᵇ β) where
  body: { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa using (zsmulRec (· • ·) n f).map_bounded' }

@[simp]

中文:
实例 instSMul整数
  签名: : 标量乘法 整数 (α ->ᵇ β) where
  定义体: { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa using (zsmulRec (· • ·) n f).map_bounded' }

@[simp]

Depends on / 依赖: f.toContinuousMap, map_bounded, toContinuousMap, zsmulRec
-/
instance instSMulInt : SMul Int (α ->ᵇ β) where
  smul n f :=
    { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa using (zsmulRec (· • ·) n f).map_bounded' }

@[simp]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (r : Int) (f : α ->ᵇ β)
  statement: ⇑(r • f) = r • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_zsmul
  条件: (r : 整数) (f : α ->ᵇ β)
  结论: ⇑(r • f) = r • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_zsmul (r : Int) (f : α ->ᵇ β) : ⇑(r • f) = r • ⇑f := rfl

@[simp]
/--
theorem `zsmul_apply` / 定理 `zsmul_apply`

English:
theorem zsmul_apply
  given: (r : Int) (f : α ->ᵇ β) (v : α)
  statement: (r • f) v = r • f v
  proof: rfl

中文:
定理 zsmul_apply
  条件: (r : 整数) (f : α ->ᵇ β) (v : α)
  结论: (r • f) v = r • f v
  证明: rfl
-/
theorem zsmul_apply (r : Int) (f : α ->ᵇ β) (v : α) : (r • f) v = r • f v := rfl

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

Depends on / 依赖: fast_instance
-/
instance instAddCommGroup : AddCommGroup (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

/--
Instance `instSeminormedAddCommGroup` / 实例 `instSeminormedAddCommGroup`

English:
instance instSeminormedAddCommGroup
  signature: : SeminormedAddCommGroup (α ->ᵇ β) where
  body: by simp only [norm_eq, dist_eq, dist_eq_norm_neg_add, add_apply, neg_apply]

中文:
实例 instSeminormedAddCommGroup
  签名: : SeminormedAddComm群 (α ->ᵇ β) where
  定义体: by simp only [norm_eq, dist_eq, dist_eq_norm_neg_add, add_apply, neg_apply]

Depends on / 依赖: add_apply, dist_eq, dist_eq_norm_neg_add, neg_apply, norm_eq
-/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (α ->ᵇ β) where
  dist_eq f g := by simp only [norm_eq, dist_eq, dist_eq_norm_neg_add, add_apply, neg_apply]

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: {α β} [TopologicalSpace α] [NormedAddCommGroup β]
  body: { instSeminormedAddCommGroup with
    eq_of_dist_eq_zero }

中文:
实例 instNormedAddCommGroup
  签名: {α β} [拓扑空间 α] [赋范交换加群 β]
  定义体: { instSeminormedAddCommGroup with
    eq_of_dist_eq_zero }

Depends on / 依赖: eq_of_dist_eq_zero, instSeminormedAddCommGroup
-/
instance instNormedAddCommGroup {α β} [TopologicalSpace α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α ->ᵇ β) :=
  { instSeminormedAddCommGroup with
    eq_of_dist_eq_zero }

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  statement: ‖f‖₊ = nndist f 0
  proof: rfl

中文:
定理 nnnorm_def
  结论: ‖f‖₊ = nndist f 0
  证明: rfl
-/
theorem nnnorm_def : ‖f‖₊ = nndist f 0 := rfl

/--
theorem `nnnorm_coe_le_nnnorm` / 定理 `nnnorm_coe_le_nnnorm`

English:
theorem nnnorm_coe_le_nnnorm
  given: (x : α)
  statement: ‖f x‖₊ <= ‖f‖₊
  proof: norm_coe_le_norm _ _

中文:
定理 nnnorm_coe_le_nnnorm
  条件: (x : α)
  结论: ‖f x‖₊ <= ‖f‖₊
  证明: norm_coe_le_norm _ _

Depends on / 依赖: norm_coe_le_norm
-/
theorem nnnorm_coe_le_nnnorm (x : α) : ‖f x‖₊ <= ‖f‖₊ :=
  norm_coe_le_norm _ _

/--
theorem `nndist_le_two_nnnorm` / 定理 `nndist_le_two_nnnorm`

English:
theorem nndist_le_two_nnnorm
  given: (x y : α)
  statement: nndist (f x) (f y) <= 2 * ‖f‖₊
  proof: dist_le_two_norm _ _ _

中文:
定理 nndist_le_two_nnnorm
  条件: (x y : α)
  结论: nndist (f x) (f y) <= 2 * ‖f‖₊
  证明: dist_le_two_norm _ _ _

Depends on / 依赖: dist_le_two_norm
-/
theorem nndist_le_two_nnnorm (x y : α) : nndist (f x) (f y) <= 2 * ‖f‖₊ :=
  dist_le_two_norm _ _ _

/--
theorem `nnnorm_le` / 定理 `nnnorm_le`

English:
theorem nnnorm_le
  given: (C : Real>=0)
  statement: ‖f‖₊ <= C ↔ forall x : α, ‖f x‖₊ <= C
  proof: norm_le C.prop

中文:
定理 nnnorm_le
  条件: (C : 实数>=0)
  结论: ‖f‖₊ <= C ↔ 对任意 x : α, ‖f x‖₊ <= C
  证明: norm_le C.prop

Depends on / 依赖: C.prop, norm_le
-/
theorem nnnorm_le (C : Real>=0) : ‖f‖₊ <= C ↔ forall x : α, ‖f x‖₊ <= C :=
  norm_le C.prop

/--
theorem `nnnorm_const_le` / 定理 `nnnorm_const_le`

English:
theorem nnnorm_const_le
  given: (b : β)
  statement: ‖const α b‖₊ <= ‖b‖₊
  proof: norm_const_le _

@[simp]

中文:
定理 nnnorm_const_le
  条件: (b : β)
  结论: ‖const α b‖₊ <= ‖b‖₊
  证明: norm_const_le _

@[simp]

Depends on / 依赖: norm_const_le
-/
theorem nnnorm_const_le (b : β) : ‖const α b‖₊ <= ‖b‖₊ :=
  norm_const_le _

@[simp]
/--
theorem `nnnorm_const_eq` / 定理 `nnnorm_const_eq`

English:
theorem nnnorm_const_eq
  given: [Nonempty α] (b : β)
  statement: ‖const α b‖₊ = ‖b‖₊
  proof: Subtype.ext norm_const_eq _

中文:
定理 nnnorm_const_eq
  条件: [非空 α] (b : β)
  结论: ‖const α b‖₊ = ‖b‖₊
  证明: Subtype.ext norm_const_eq _

Depends on / 依赖: Subtype, Subtype.ext, norm_const_eq
-/
theorem nnnorm_const_eq [Nonempty α] (b : β) : ‖const α b‖₊ = ‖b‖₊ :=
Subtype.ext norm_const_eq _

/--
theorem `nnnorm_eq_iSup_nnnorm` / 定理 `nnnorm_eq_iSup_nnnorm`

English:
theorem nnnorm_eq_iSup_nnnorm
  statement: ‖f‖₊ = ⨆ x : α, ‖f x‖₊
  proof: Subtype.ext (norm_eq_iSup_norm f).trans by simp_rw [val_eq_coe, NNReal.coe_iSup, coe_nnnorm]

中文:
定理 nnnorm_eq_iSup_nnnorm
  结论: ‖f‖₊ = ⨆ x : α, ‖f x‖₊
  证明: Subtype.ext (norm_eq_iSup_norm f).trans by simp_rw [val_eq_coe, NNReal.coe_iSup, coe_nnnorm]

Depends on / 依赖: NNReal, NNReal.coe_iSup, Subtype, Subtype.ext, coe_iSup, coe_nnnorm, norm_eq_iSup_norm, simp_rw, val_eq_coe
-/
theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
Subtype.ext (norm_eq_iSup_norm f).trans by simp_rw [val_eq_coe, NNReal.coe_iSup, coe_nnnorm]

/--
theorem `enorm_eq_iSup_enorm` / 定理 `enorm_eq_iSup_enorm`

English:
theorem enorm_eq_iSup_enorm
  statement: ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
  proof: by
  simpa only [← edist_zero_right] using! edist_eq_iSup

中文:
定理 enorm_eq_iSup_enorm
  结论: ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
  证明: by
  simpa only [← edist_zero_right] using! edist_eq_iSup

Depends on / 依赖: edist_eq_iSup, edist_zero_right
-/
theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ := by
  simpa only [← edist_zero_right] using! edist_eq_iSup

/--
theorem `abs_sub_coe_le_dist` / 定理 `abs_sub_coe_le_dist`

English:
theorem abs_sub_coe_le_dist
  statement: ‖f x - g x‖ <= dist f g
  proof: by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

@[deprecated (since := "2026-06-03")] alias abs_diff_coe_le_dist := abs_sub_coe_le_dist

中文:
定理 abs_sub_coe_le_dist
  结论: ‖f x - g x‖ <= dist f g
  证明: by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

@[deprecated (since := "2026-06-03")] alias abs_diff_coe_le_dist := abs_sub_coe_le_dist

Depends on / 依赖: dist_eq_norm, norm_coe_le_norm
-/
theorem abs_sub_coe_le_dist : ‖f x - g x‖ <= dist f g := by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

@[deprecated (since := "2026-06-03")] alias abs_diff_coe_le_dist := abs_sub_coe_le_dist

/--
theorem `coe_le_coe_add_dist` / 定理 `coe_le_coe_add_dist`

English:
theorem coe_le_coe_add_dist
  given: {f g : α ->ᵇ Real}
  statement: f x <= g x + dist f g
  proof: sub_le_iff_le_add'.1 (abs_le.1 <| @dist_coe_le_dist _ _ _ _ f g x).2

中文:
定理 coe_le_coe_add_dist
  条件: {f g : α ->ᵇ 实数}
  结论: f x <= g x + dist f g
  证明: sub_le_iff_le_add'.1 (abs_le.1 <| @dist_coe_le_dist _ _ _ _ f g x).2

Depends on / 依赖: abs_le, dist_coe_le_dist, sub_le_iff_le_add
-/
theorem coe_le_coe_add_dist {f g : α ->ᵇ Real} : f x <= g x + dist f g :=
sub_le_iff_le_add'.1 (abs_le.1 <| @dist_coe_le_dist _ _ _ _ f g x).2

/--
theorem `norm_compContinuous_le` / 定理 `norm_compContinuous_le`

English:
theorem norm_compContinuous_le
  given: [TopologicalSpace γ] (f : α ->ᵇ β) (g : C(γ, α))
  proof: ((lipschitz_compContinuous g).dist_le_mul f 0).trans by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_zero_right]

中文:
定理 norm_compContinuous_le
  条件: [拓扑空间 γ] (f : α ->ᵇ β) (g : C(γ, α))
  证明: ((lipschitz_compContinuous g).dist_le_mul f 0).trans by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_zero_right]

Depends on / 依赖: NNReal, NNReal.coe_one, coe_one, dist_le_mul, dist_zero_right, lipschitz_compContinuous, one_mul
-/
theorem norm_compContinuous_le [TopologicalSpace γ] (f : α ->ᵇ β) (g : C(γ, α)) :
    ‖f.compContinuous g‖ <= ‖f‖ :=
((lipschitz_compContinuous g).dist_le_mul f 0).trans by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_zero_right]

end NormedAddCommGroup

section NormedSpace

variable {𝕜 : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable {f g : α ->ᵇ β} {x : α} {C : Real}

/--
Instance `instNormedSpace` / 实例 `instNormedSpace`

English:
instance instNormedSpace
  signature: [NormedField 𝕜] [NormedSpace 𝕜 β]
  body: ⟨fun c f => by
    refine norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

中文:
实例 instNormedSpace
  签名: [赋范域 𝕜] [赋范空间 𝕜 β]
  定义体: ⟨fun c f => by
    refine norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

Depends on / 依赖: f.norm_coe_le_norm, mul_le_mul_of_nonneg_left, mul_nonneg, norm_coe_le_norm, norm_nonneg, norm_ofNormedAddCommGroup_le, norm_smul
-/
instance instNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α ->ᵇ β) :=
  ⟨fun c f => by
    refine norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β]

section compLeftContinuousBounded

variable [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]

variable (α) in
-- TODO does this work in the `IsBoundedSMul` setting, too?
/--
Definition of `_root_.ContinuousLinearMap.compLeftContinuousBounded` / `_root_.ContinuousLinearMap.compLeftContinuousBounded` 的定义

English:
definition _root_.ContinuousLinearMap.compLeftContinuousBounded
  signature: (g : β ->L[𝕜] γ)
  body: LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        nor

中文:
定义 _root_.连续线性映射.compLeftContinuousBounded
  签名: (g : β ->L[𝕜] γ)
  定义体: LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        nor
-/
protected def _root_.ContinuousLinearMap.compLeftContinuousBounded (g : β ->L[𝕜] γ) :
    (α ->ᵇ β) ->L[𝕜] α ->ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f))
          (fun x => by exact g.le_opNorm_of_le (f.norm_coe_le_norm x))

@[simp]
/--
theorem `_root_.ContinuousLinearMap.compLeftContinuousBounded_apply` / 定理 `_root_.ContinuousLinearMap.compLeftContinuousBounded_apply`

English:
theorem _root_.ContinuousLinearMap.compLeftContinuousBounded_apply
  statement: (g : β ->L[𝕜] γ) (f : α ->ᵇ β)
  proof: rfl

中文:
定理 _root_.连续线性映射.compLeftContinuousBounded_apply
  结论: (g : β ->L[𝕜] γ) (f : α ->ᵇ β)
  证明: rfl
-/
theorem _root_.ContinuousLinearMap.compLeftContinuousBounded_apply (g : β ->L[𝕜] γ) (f : α ->ᵇ β)
    (x : α) : (g.compLeftContinuousBounded α f) x = g (f x) := rfl

end compLeftContinuousBounded

section compContinuousCLM

variable {𝕜 : Type*}

section NormedField

variable [TopologicalSpace γ] [NormedField 𝕜] [NormedSpace 𝕜 β]

variable (β 𝕜) in
/--
Definition of `compContinuousCLM` / `compContinuousCLM` 的定义

English:
definition compContinuousCLM
  signature: (g : C(γ, α))
  body: LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

@[simp]

中文:
定义 compContinuousCLM
  签名: (g : C(γ, α))
  定义体: LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, compContinuous, f.compContinuous, intros, map_add, map_smul, mkContinuous, norm_compContinuous_le
-/
def compContinuousCLM (g : C(γ, α)) : (α ->ᵇ β) ->L[𝕜] γ ->ᵇ β :=
  LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

@[simp]
/--
theorem `compContinuousCLM_apply` / 定理 `compContinuousCLM_apply`

English:
theorem compContinuousCLM_apply
  given: (f : α ->ᵇ β) (g : C(γ, α))
  proof: rfl

中文:
定理 compContinuousCLM_apply
  条件: (f : α ->ᵇ β) (g : C(γ, α))
  证明: rfl
-/
theorem compContinuousCLM_apply (f : α ->ᵇ β) (g : C(γ, α)) :
  f.compContinuousCLM β 𝕜 g = f.compContinuous g := rfl

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β] [SeminormedAddCommGroup γ]

/--
theorem `norm_compContinuousCLM_le_one` / 定理 `norm_compContinuousCLM_le_one`

English:
theorem norm_compContinuousCLM_le_one
  given: (g : C(γ, α))
  statement: ‖compContinuousCLM β 𝕜 g‖ <= 1
  proof: by
  refine (compContinuousCLM β 𝕜 g).opNorm_le_bound zero_le_one (fun x => ?_)
  simpa using norm_compContinuous_le x g

中文:
定理 norm_compContinuousCLM_le_one
  条件: (g : C(γ, α))
  结论: ‖compContinuousCLM β 𝕜 g‖ <= 1
  证明: by
  refine (compContinuousCLM β 𝕜 g).opNorm_le_bound zero_le_one (fun x => ?_)
  simpa using norm_compContinuous_le x g

Depends on / 依赖: compContinuousCLM, norm_compContinuous_le, opNorm_le_bound, zero_le_one
-/
theorem norm_compContinuousCLM_le_one (g : C(γ, α)) : ‖compContinuousCLM β 𝕜 g‖ <= 1 := by
  refine (compContinuousCLM β 𝕜 g).opNorm_le_bound zero_le_one (fun x => ?_)
  simpa using norm_compContinuous_le x g

end NontriviallyNormedField

end compContinuousCLM

end NormedSpace

section NormedRing

variable [TopologicalSpace α] {R : Type*}

section NonUnital

section Seminormed

variable [NonUnitalSeminormedRing R]

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: : NonUnitalRing (α ->ᵇ R)
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

中文:
实例 instNonUnitalRing
  签名: : 非幺环 (α ->ᵇ R)
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

Depends on / 依赖: fast_instance
-/
instance instNonUnitalRing : NonUnitalRing (α ->ᵇ R) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

/--
Instance `instNonUnitalSeminormedRing` / 实例 `instNonUnitalSeminormedRing`

English:
instance instNonUnitalSeminormedRing
  signature: : NonUnitalSeminormedRing (α ->ᵇ R) where
  body: instSeminormedAddCommGroup
  __ := instNonUnitalRing
  norm_mul_le f g := norm_ofNormedAddCommGroup_le _ (by positivity)
    (fun x => (norm_mul_le _ _).trans <| mul_le_mul
      (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _))

中文:
实例 instNonUnitalSeminormedRing
  签名: : 非幺Seminormed环 (α ->ᵇ R) where
  定义体: instSeminormedAddCommGroup
  __ := instNonUnitalRing
  norm_mul_le f g := norm_ofNormedAddCommGroup_le _ (by positivity)
    (fun x => (norm_mul_le _ _).trans <| mul_le_mul
      (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _))

Depends on / 依赖: instSeminormedAddCommGroup
-/
instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing (α ->ᵇ R) where
  __ := instSeminormedAddCommGroup
  __ := instNonUnitalRing
  norm_mul_le f g := norm_ofNormedAddCommGroup_le _ (by positivity)
    (fun x => (norm_mul_le _ _).trans <| mul_le_mul
      (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _))

/--
lemma `norm_add_eq_max` / 引理 `norm_add_eq_max`

English:
lemma norm_add_eq_max
  given: [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0)
  proof: by
  have hfg : forall x, f x = 0 ∨ g x = 0 := by simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' x : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by obtain (h | h) := hfg x <;> simp [h]
  have key (c : Real) (hc : 0 <= c) : ‖f + g‖ <= c ↔ max ‖f‖ ‖g‖ <= c := by
    simp_rw [norm_le hc, hfg', max_le_i

中文:
引理 norm_add_eq_max
  条件: [是乘零消去 R] {f g : α ->ᵇ R} (h : f * g = 0)
  证明: by
  have hfg : forall x, f x = 0 ∨ g x = 0 := by simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' x : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by obtain (h | h) := hfg x <;> simp [h]
  have key (c : Real) (hc : 0 <= c) : ‖f + g‖ <= c ↔ max ‖f‖ ‖g‖ <= c := by
    simp_rw [norm_le hc, hfg', max_le_i

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, forall_and, le_antisymm, max_le_iff, mul_eq_zero, norm_le, simp_rw
-/
lemma norm_add_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  have hfg : forall x, f x = 0 ∨ g x = 0 := by simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' x : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by obtain (h | h) := hfg x <;> simp [h]
  have key (c : Real) (hc : 0 <= c) : ‖f + g‖ <= c ↔ max ‖f‖ ‖g‖ <= c := by
    simp_rw [norm_le hc, hfg', max_le_iff, norm_le hc, forall_and]
  exact le_antisymm (by rw [key]; positivity) (by rw [← key]; positivity)

/--
lemma `nnnorm_add_eq_max` / 引理 `nnnorm_add_eq_max`

English:
lemma nnnorm_add_eq_max
  given: [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0)
  proof: NNReal.eq norm_add_eq_max h

中文:
引理 nnnorm_add_eq_max
  条件: [是乘零消去 R] {f g : α ->ᵇ R} (h : f * g = 0)
  证明: NNReal.eq norm_add_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_add_eq_max
-/
lemma nnnorm_add_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) :
    ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊ :=
NNReal.eq norm_add_eq_max h

/--
lemma `norm_sub_eq_max` / 引理 `norm_sub_eq_max`

English:
lemma norm_sub_eq_max
  given: [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0)
  proof: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

中文:
引理 norm_sub_eq_max
  条件: [是乘零消去 R] {f g : α ->ᵇ R} (h : f * g = 0)
  证明: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

Depends on / 依赖: norm_add_eq_max, sub_eq_add_neg
-/
lemma norm_sub_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) :
    ‖f - g‖ = max ‖f‖ ‖g‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

/--
lemma `nnnorm_sub_eq_max` / 引理 `nnnorm_sub_eq_max`

English:
lemma nnnorm_sub_eq_max
  given: [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0)
  proof: NNReal.eq norm_sub_eq_max h

中文:
引理 nnnorm_sub_eq_max
  条件: [是乘零消去 R] {f g : α ->ᵇ R} (h : f * g = 0)
  证明: NNReal.eq norm_sub_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_sub_eq_max
-/
lemma nnnorm_sub_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) :
    ‖f - g‖₊ = max ‖f‖₊ ‖g‖₊ :=
NNReal.eq norm_sub_eq_max h

open scoped Function in
/--
lemma `nnnorm_sum_eq_sup` / 引理 `nnnorm_sum_eq_sup`

English:
lemma nnnorm_sum_eq_sup
  statement: [IsCancelMulZero R] {ι : Type*} {f : ι -> (α ->ᵇ R)} (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

中文:
引理 nnnorm_sum_eq_sup
  结论: [是乘零消去 R] {ι : 类型} {f : ι -> (α ->ᵇ R)} (s : 有限集 ι)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mul_sum, Finset.sum_eq_zero, classical, induction_on, insert, mul_sum, nnnorm_add_eq_max, sum_eq_zero
-/
lemma nnnorm_sum_eq_sup [IsCancelMulZero R] {ι : Type*} {f : ι -> (α ->ᵇ R)} (s : Finset ι)
    (h : Pairwise ((· * · = 0) on f)) :
    ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

end Seminormed

/--
Instance `instNonUnitalSeminormedCommRing` / 实例 `instNonUnitalSeminormedCommRing`

English:
instance instNonUnitalSeminormedCommRing
  signature: [NonUnitalSeminormedCommRing R]
  body: ext fun _ => mul_comm ..

中文:
实例 instNonUnitalSeminormedCommRing
  签名: [非幺SeminormedComm环 R]
  定义体: ext fun _ => mul_comm ..

Depends on / 依赖: mul_comm
-/
instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing R] :
    NonUnitalSeminormedCommRing (α ->ᵇ R) where
  mul_comm _ _ := ext fun _ => mul_comm ..

/--
Instance `instNonUnitalNormedRing` / 实例 `instNonUnitalNormedRing`

English:
instance instNonUnitalNormedRing
  signature: [NonUnitalNormedRing R]
  body: instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

中文:
实例 instNonUnitalNormedRing
  签名: [非幺赋范环 R]
  定义体: instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

Depends on / 依赖: instNonUnitalSeminormedRing
-/
instance instNonUnitalNormedRing [NonUnitalNormedRing R] : NonUnitalNormedRing (α ->ᵇ R) where
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

/--
Instance `instNonUnitalNormedCommRing` / 实例 `instNonUnitalNormedCommRing`

English:
instance instNonUnitalNormedCommRing
  signature: [NonUnitalNormedCommRing R]
  body: mul_comm

中文:
实例 instNonUnitalNormedCommRing
  签名: [非幺NormedComm环 R]
  定义体: mul_comm

Depends on / 依赖: mul_comm
-/
instance instNonUnitalNormedCommRing [NonUnitalNormedCommRing R] :
    NonUnitalNormedCommRing (α ->ᵇ R) where
  mul_comm := mul_comm

end NonUnital

section Seminormed

variable [SeminormedRing R]

@[simp]
/--
theorem `coe_npowRec` / 定理 `coe_npowRec`

English:
theorem coe_npowRec
  given: (f : α ->ᵇ R)
  statement: forall n, ⇑(npowRec n f) = (⇑f) ^ n

中文:
定理 coe_npowRec
  条件: (f : α ->ᵇ R)
  结论: 对任意 n, ⇑(npowRec n f) = (⇑f) ^ n
-/
theorem coe_npowRec (f : α ->ᵇ R) : forall n, ⇑(npowRec n f) = (⇑f) ^ n
  | 0 => by rw [npowRec, pow_zero, coe_one]
  | n + 1 => by rw [npowRec, pow_succ, coe_mul, coe_npowRec f n]

/--
Instance `hasNatPow` / 实例 `hasNatPow`

English:
instance hasNatPow
  signature: : Pow (α ->ᵇ R) Nat where
  body: { toContinuousMap := f.toContinuousMap ^ n
      map_bounded' := by simpa [coe_npowRec] using (npowRec n f).map_bounded' }

中文:
实例 has自然数Pow
  签名: : 幂 (α ->ᵇ R) 自然数 where
  定义体: { toContinuousMap := f.toContinuousMap ^ n
      map_bounded' := by simpa [coe_npowRec] using (npowRec n f).map_bounded' }

Depends on / 依赖: coe_npowRec, f.toContinuousMap, map_bounded, npowRec, toContinuousMap
-/
instance hasNatPow : Pow (α ->ᵇ R) Nat where
  pow f n :=
    { toContinuousMap := f.toContinuousMap ^ n
      map_bounded' := by simpa [coe_npowRec] using (npowRec n f).map_bounded' }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (α ->ᵇ R)
  body: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 自然数嵌入 (α ->ᵇ R)
  定义体: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.const
-/
instance : NatCast (α ->ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : α ->ᵇ R) : α -> R) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : α ->ᵇ R) : α -> R) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_natCast (n : Nat) : ((n : α ->ᵇ R) : α -> R) = n := rfl

@[simp, norm_cast]
/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
theorem coe_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : α ->ᵇ R) : α -> R) = ofNat(n) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (α ->ᵇ R)
  body: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 整数嵌入 (α ->ᵇ R)
  定义体: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.const
-/
instance : IntCast (α ->ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (n : Int)
  statement: ((n : α ->ᵇ R) : α -> R) = n
  proof: rfl

中文:
定理 coe_intCast
  条件: (n : 整数)
  结论: ((n : α ->ᵇ R) : α -> R) = n
  证明: rfl
-/
theorem coe_intCast (n : Int) : ((n : α ->ᵇ R) : α -> R) = n := rfl

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (α ->ᵇ R)
  body: fast_instance%
  DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) (fun _ _ => coe_zsmul _ _) (fun _ _ => coe_pow _ _) coe_natCast
    coe_intCast

中文:
实例 instRing
  签名: : 环 (α ->ᵇ R)
  定义体: fast_instance%
  DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) (fun _ _ => coe_zsmul _ _) (fun _ _ => coe_pow _ _) coe_natCast
    coe_intCast

Depends on / 依赖: fast_instance
-/
instance instRing : Ring (α ->ᵇ R) := fast_instance%
  DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) (fun _ _ => coe_zsmul _ _) (fun _ _ => coe_pow _ _) coe_natCast
    coe_intCast

/--
Instance `instSeminormedRing` / 实例 `instSeminormedRing`

English:
instance instSeminormedRing
  signature: : SeminormedRing (α ->ᵇ R) where
  body: instRing
  __ := instNonUnitalSeminormedRing

中文:
实例 instSeminormedRing
  签名: : Seminormed环 (α ->ᵇ R) where
  定义体: instRing
  __ := instNonUnitalSeminormedRing

Depends on / 依赖: instRing
-/
instance instSeminormedRing : SeminormedRing (α ->ᵇ R) where
  __ := instRing
  __ := instNonUnitalSeminormedRing

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological semirings, as a
`RingHom`. Similar to `RingHom.compLeftContinuous`. -/
@[simps!]
/--
Definition of `_root_.RingHom.compLeftContinuousBounded` / `_root_.RingHom.compLeftContinuousBounded` 的定义

English:
definition _root_.RingHom.compLeftContinuousBounded
  signature: (α : Type*)
  body: { g.toMonoidHom.compLeftContinuousBounded α hg,
    g.toAddMonoidHom.compLeftContinuousBounded α hg with }

中文:
定义 _root_.环态射.compLeftContinuousBounded
  签名: (α : 类型)
  定义体: { g.toMonoidHom.compLeftContinuousBounded α hg,
    g.toAddMonoidHom.compLeftContinuousBounded α hg with }
-/
protected def _root_.RingHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [SeminormedRing β] [SeminormedRing γ]
    (g : β ->+* γ) {C : NNReal} (hg : LipschitzWith C g) : (α ->ᵇ β) ->+* (α ->ᵇ γ) :=
  { g.toMonoidHom.compLeftContinuousBounded α hg,
    g.toAddMonoidHom.compLeftContinuousBounded α hg with }

end Seminormed

/--
Instance `instNormedRing` / 实例 `instNormedRing`

English:
instance instNormedRing
  signature: [NormedRing R]
  body: instRing
  __ := instNonUnitalNormedRing

中文:
实例 instNormedRing
  签名: [赋范环 R]
  定义体: instRing
  __ := instNonUnitalNormedRing

Depends on / 依赖: instRing
-/
instance instNormedRing [NormedRing R] : NormedRing (α ->ᵇ R) where
  __ := instRing
  __ := instNonUnitalNormedRing

end NormedRing

section NormedCommRing

variable [TopologicalSpace α] {R : Type*}

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [SeminormedCommRing R]
  body: ext fun _ => mul_comm _ _

中文:
实例 instCommRing
  签名: [SeminormedComm环 R]
  定义体: ext fun _ => mul_comm _ _

Depends on / 依赖: mul_comm
-/
instance instCommRing [SeminormedCommRing R] : CommRing (α ->ᵇ R) where
  mul_comm _ _ := ext fun _ => mul_comm _ _

/--
Instance `instSeminormedCommRing` / 实例 `instSeminormedCommRing`

English:
instance instSeminormedCommRing
  signature: [SeminormedCommRing R]
  body: instCommRing
  __ := instNonUnitalSeminormedRing

中文:
实例 instSeminormedCommRing
  签名: [SeminormedComm环 R]
  定义体: instCommRing
  __ := instNonUnitalSeminormedRing

Depends on / 依赖: instCommRing
-/
instance instSeminormedCommRing [SeminormedCommRing R] : SeminormedCommRing (α ->ᵇ R) where
  __ := instCommRing
  __ := instNonUnitalSeminormedRing

/--
Instance `instNormedCommRing` / 实例 `instNormedCommRing`

English:
instance instNormedCommRing
  signature: [NormedCommRing R]
  body: instSeminormedCommRing
  __ := instNormedAddCommGroup

中文:
实例 instNormedCommRing
  签名: [NormedComm环 R]
  定义体: instSeminormedCommRing
  __ := instNormedAddCommGroup

Depends on / 依赖: instSeminormedCommRing
-/
instance instNormedCommRing [NormedCommRing R] : NormedCommRing (α ->ᵇ R) where
  __ := instSeminormedCommRing
  __ := instNormedAddCommGroup

end NormedCommRing

section NonUnitalAlgebra

-- these hypotheses could be generalized if we generalize `IsBoundedSMul` to `Bornology`.
variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [NonUnitalSeminormedRing β]
variable [Zero 𝕜] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScalarTower
  signature: 𝕜 β β] : IsScalarTower 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  body: ext fun _ => smul_mul_assoc ..

中文:
实例 [标量塔
  签名: 𝕜 β β] : 标量塔 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  定义体: ext fun _ => smul_mul_assoc ..

Depends on / 依赖: smul_mul_assoc
-/
instance [IsScalarTower 𝕜 β β] : IsScalarTower 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  smul_assoc _ _ _ := ext fun _ => smul_mul_assoc ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: 𝕜 β β] : SMulCommClass 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  body: ext fun _ => (mul_smul_comm ..).symm

中文:
实例 [标量交换类
  签名: 𝕜 β β] : 标量交换类 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  定义体: ext fun _ => (mul_smul_comm ..).symm

Depends on / 依赖: mul_smul_comm
-/
instance [SMulCommClass 𝕜 β β] : SMulCommClass 𝕜 (α ->ᵇ β) (α ->ᵇ β) where
  smul_comm _ _ _ := ext fun _ => (mul_smul_comm ..).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: 𝕜 β β] : SMulCommClass (α ->ᵇ β) 𝕜 (α ->ᵇ β) where
  body: ext fun _ => mul_smul_comm ..

中文:
实例 [标量交换类
  签名: 𝕜 β β] : 标量交换类 (α ->ᵇ β) 𝕜 (α ->ᵇ β) where
  定义体: ext fun _ => mul_smul_comm ..

Depends on / 依赖: mul_smul_comm
-/
instance [SMulCommClass 𝕜 β β] : SMulCommClass (α ->ᵇ β) 𝕜 (α ->ᵇ β) where
  smul_comm _ _ _ := ext fun _ => mul_smul_comm ..

end NonUnitalAlgebra

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [TopologicalSpace α]
variable [NormedRing γ] [NormedAlgebra 𝕜 γ]

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : 𝕜 ->+* α ->ᵇ γ where
  body: fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _

中文:
定义 C
  签名: : 𝕜 ->+* α ->ᵇ γ where
  定义体: fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _

Depends on / 依赖: algebraMap
-/
def C : 𝕜 ->+* α ->ᵇ γ where
  toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra 𝕜 (α ->ᵇ γ) where
  body: C
  commutes' _ _ := ext fun _ => Algebra.commutes' _ _
  smul_def' _ _ := ext fun _ => Algebra.smul_def' _ _

@[simp]

中文:
实例 instAlgebra
  签名: : 代数 𝕜 (α ->ᵇ γ) where
  定义体: C
  commutes' _ _ := ext fun _ => Algebra.commutes' _ _
  smul_def' _ _ := ext fun _ => Algebra.smul_def' _ _

@[simp]
-/
instance instAlgebra : Algebra 𝕜 (α ->ᵇ γ) where
  algebraMap := C
  commutes' _ _ := ext fun _ => Algebra.commutes' _ _
  smul_def' _ _ := ext fun _ => Algebra.smul_def' _ _

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (k : 𝕜) (a : α)
  statement: algebraMap 𝕜 (α ->ᵇ γ) k a = k • (1 : γ)
  proof: by
  simp only [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one, Pi.one_apply]

中文:
定理 algebraMap_apply
  条件: (k : 𝕜) (a : α)
  结论: algebraMap 𝕜 (α ->ᵇ γ) k a = k • (1 : γ)
  证明: by
  simp only [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one, Pi.one_apply]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Pi.one_apply, algebraMap_eq_smul_one, coe_one, coe_smul, one_apply
-/
theorem algebraMap_apply (k : 𝕜) (a : α) : algebraMap 𝕜 (α ->ᵇ γ) k a = k • (1 : γ) := by
  simp only [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one, Pi.one_apply]

/--
Instance `instNormedAlgebra` / 实例 `instNormedAlgebra`

English:
instance instNormedAlgebra
  signature: : NormedAlgebra 𝕜 (α ->ᵇ γ) where
  body: instAlgebra
  __ := instNormedSpace

中文:
实例 instNormedAlgebra
  签名: : 赋范代数 𝕜 (α ->ᵇ γ) where
  定义体: instAlgebra
  __ := instNormedSpace

Depends on / 依赖: instAlgebra
-/
instance instNormedAlgebra : NormedAlgebra 𝕜 (α ->ᵇ γ) where
  __ := instAlgebra
  __ := instNormedSpace

variable (𝕜)

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `R`-algebras,
as an `AlgHom`. Similar to `AlgHom.compLeftContinuous`. -/
@[simps!]
/--
Definition of `AlgHom.compLeftContinuousBounded` / `AlgHom.compLeftContinuousBounded` 的定义

English:
definition AlgHom.compLeftContinuousBounded
  signature: [NormedRing β] [NormedAlgebra 𝕜 β]
  body: { g.toRingHom.compLeftContinuousBounded α hg with
    commutes' := fun _ => DFunLike.ext _ _ fun _ => g.commutes' _ }

中文:
定义 代数态射.compLeftContinuousBounded
  签名: [赋范环 β] [赋范代数 𝕜 β]
  定义体: { g.toRingHom.compLeftContinuousBounded α hg with
    commutes' := fun _ => DFunLike.ext _ _ fun _ => g.commutes' _ }
-/
protected def AlgHom.compLeftContinuousBounded [NormedRing β] [NormedAlgebra 𝕜 β]
    (g : β ->ₐ[𝕜] γ) {C : NNReal} (hg : LipschitzWith C g) : (α ->ᵇ β) ->ₐ[𝕜] (α ->ᵇ γ) :=
  { g.toRingHom.compLeftContinuousBounded α hg with
    commutes' := fun _ => DFunLike.ext _ _ fun _ => g.commutes' _ }

/-- The algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps]
/--
Definition of `toContinuousMapₐ` / `toContinuousMapₐ` 的定义

English:
definition toContinuousMapₐ
  signature: : (α ->ᵇ γ) ->ₐ[𝕜] C(α, γ) where
  body: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]

中文:
定义 toContinuousMapₐ
  签名: : (α ->ᵇ γ) ->ₐ[𝕜] C(α, γ) where
  定义体: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
-/
def toContinuousMapₐ : (α ->ᵇ γ) ->ₐ[𝕜] C(α, γ) where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
/--
theorem `coe_toContinuousMapₐ` / 定理 `coe_toContinuousMapₐ`

English:
theorem coe_toContinuousMapₐ
  given: (f : α ->ᵇ γ)
  statement: (f.toContinuousMapₐ 𝕜 : α -> γ) = f
  proof: rfl

中文:
定理 coe_toContinuousMapₐ
  条件: (f : α ->ᵇ γ)
  结论: (f.toContinuousMapₐ 𝕜 : α -> γ) = f
  证明: rfl
-/
theorem coe_toContinuousMapₐ (f : α ->ᵇ γ) : (f.toContinuousMapₐ 𝕜 : α -> γ) = f := rfl

variable {𝕜} [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]


/--
Instance `instSMul'` / 实例 `instSMul'`

English:
instance instSMul'
  signature: : SMul (α ->ᵇ 𝕜) (α ->ᵇ β) where
  body: ofNormedAddCommGroup (fun x => f x • g x) (f.continuous.smul g.continuous) (‖f‖ * ‖g‖) fun x =>
      calc
        ‖f x • g x‖ <= ‖f x‖ * ‖g x‖ := norm_smul_le _ _
        _ <= ‖f‖ * ‖g‖ :=
          mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

中文:
实例 instSMul'
  签名: : 标量乘法 (α ->ᵇ 𝕜) (α ->ᵇ β) where
  定义体: ofNormedAddCommGroup (fun x => f x • g x) (f.continuous.smul g.continuous) (‖f‖ * ‖g‖) fun x =>
      calc
        ‖f x • g x‖ <= ‖f x‖ * ‖g x‖ := norm_smul_le _ _
        _ <= ‖f‖ * ‖g‖ :=
          mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

Depends on / 依赖: continuous, f.continuous.smul, f.norm_coe_le_norm, g.continuous, g.norm_coe_le_norm, mul_le_mul, norm_coe_le_norm, norm_nonneg, norm_smul_le, ofNormedAddCommGroup
-/
instance instSMul' : SMul (α ->ᵇ 𝕜) (α ->ᵇ β) where
  smul f g :=
    ofNormedAddCommGroup (fun x => f x • g x) (f.continuous.smul g.continuous) (‖f‖ * ‖g‖) fun x =>
      calc
        ‖f x • g x‖ <= ‖f x‖ * ‖g x‖ := norm_smul_le _ _
        _ <= ‖f‖ * ‖g‖ :=
          mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: : Module (α ->ᵇ 𝕜) (α ->ᵇ β)
  body: Module.ofMinimalAxioms
      (fun c _ _ => ext fun a => smul_add (c a) _ _)
      (fun _ _ _ => ext fun _ => add_smul _ _ _)
      (fun _ _ _ => ext fun _ => mul_smul _ _ _)
      (fun f => ext fun x => one_smul 𝕜 (f x))

中文:
实例 instModule'
  签名: : 模 (α ->ᵇ 𝕜) (α ->ᵇ β)
  定义体: Module.ofMinimalAxioms
      (fun c _ _ => ext fun a => smul_add (c a) _ _)
      (fun _ _ _ => ext fun _ => add_smul _ _ _)
      (fun _ _ _ => ext fun _ => mul_smul _ _ _)
      (fun f => ext fun x => one_smul 𝕜 (f x))

Depends on / 依赖: Module, Module.ofMinimalAxioms, add_smul, mul_smul, ofMinimalAxioms, one_smul, smul_add
-/
instance instModule' : Module (α ->ᵇ 𝕜) (α ->ᵇ β) :=
  Module.ofMinimalAxioms
      (fun c _ _ => ext fun a => smul_add (c a) _ _)
      (fun _ _ _ => ext fun _ => add_smul _ _ _)
      (fun _ _ _ => ext fun _ => mul_smul _ _ _)
      (fun f => ext fun x => one_smul 𝕜 (f x))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBoundedSMul (α ->ᵇ 𝕜) (α ->ᵇ β)
  body: IsBoundedSMul.of_norm_smul_le fun _ _ =>
    norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

中文:
实例 :
  签名: 是BoundedSMul (α ->ᵇ 𝕜) (α ->ᵇ β)
  定义体: IsBoundedSMul.of_norm_smul_le fun _ _ =>
    norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.of_norm_smul_le, mul_nonneg, norm_nonneg, norm_ofNormedAddCommGroup_le, of_norm_smul_le
-/
instance : IsBoundedSMul (α ->ᵇ 𝕜) (α ->ᵇ β) :=
  IsBoundedSMul.of_norm_smul_le fun _ _ =>
    norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

end NormedAlgebra

section NormedLatticeOrderedGroup

variable [TopologicalSpace α]
  [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (α ->ᵇ β)
  body: PartialOrder.lift (fun f => f.toFun) (by simp [Injective])

中文:
实例 instPartialOrder
  签名: : 偏序 (α ->ᵇ β)
  定义体: PartialOrder.lift (fun f => f.toFun) (by simp [Injective])

Depends on / 依赖: Injective, PartialOrder, PartialOrder.lift, f.toFun
-/
instance instPartialOrder : PartialOrder (α ->ᵇ β) :=
  PartialOrder.lift (fun f => f.toFun) (by simp [Injective])

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (α ->ᵇ β) where
  body: { toFun := f ⊔ g
      continuous_toFun := f.continuous.sup g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_sup_sub_sup_le_add_nor

中文:
实例 instSup
  签名: : 最大值 (α ->ᵇ β) where
  定义体: { toFun := f ⊔ g
      continuous_toFun := f.continuous.sup g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_sup_sub_sup_le_add_nor

Depends on / 依赖: add_le_add, bounded, continuous, continuous_toFun, dist_eq_norm_sub, f.bounded, f.continuous.sup, g.bounded, g.continuous, map_bounded, norm_sup_sub_sup_le_add_norm, simp_rw
-/
instance instSup : Max (α ->ᵇ β) where
  max f g :=
    { toFun := f ⊔ g
      continuous_toFun := f.continuous.sup g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_sup_sub_sup_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (α ->ᵇ β) where
  body: { toFun := f ⊓ g
      continuous_toFun := f.continuous.inf g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_inf_sub_inf_le_add_nor

中文:
实例 instInf
  签名: : 最小值 (α ->ᵇ β) where
  定义体: { toFun := f ⊓ g
      continuous_toFun := f.continuous.inf g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_inf_sub_inf_le_add_nor

Depends on / 依赖: add_le_add, bounded, continuous, continuous_toFun, dist_eq_norm_sub, f.bounded, f.continuous.inf, g.bounded, g.continuous, map_bounded, norm_inf_sub_inf_le_add_norm, simp_rw
-/
instance instInf : Min (α ->ᵇ β) where
  min f g :=
    { toFun := f ⊓ g
      continuous_toFun := f.continuous.inf g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_inf_sub_inf_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (f g : α ->ᵇ β)
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

中文:
引理 coe_sup
  条件: (f g : α ->ᵇ β)
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (f g : α ->ᵇ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g := rfl

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (f g : α ->ᵇ β)
  statement: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  proof: rfl

中文:
引理 coe_inf
  条件: (f g : α ->ᵇ β)
  结论: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (f g : α ->ᵇ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g := rfl

/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: fast_instance
-/
instance instSemilatticeSup : SemilatticeSup (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

Depends on / 依赖: fast_instance
-/
instance instSemilatticeInf : SemilatticeInf (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf

中文:
实例 instLattice
  签名: : 格 (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf

Depends on / 依赖: fast_instance
-/
instance instLattice : Lattice (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf

/--
lemma `coe_abs` / 引理 `coe_abs`

English:
lemma coe_abs
  given: (f : α ->ᵇ β)
  statement: ⇑|f| = |⇑f|
  proof: rfl

中文:
引理 coe_abs
  条件: (f : α ->ᵇ β)
  结论: ⇑|f| = |⇑f|
  证明: rfl
-/
@[simp, norm_cast] lemma coe_abs (f : α ->ᵇ β) : ⇑|f| = |⇑f| := rfl
/--
lemma `coe_posPart` / 引理 `coe_posPart`

English:
lemma coe_posPart
  given: (f : α ->ᵇ β)
  statement: ⇑f⁺ = (⇑f)⁺
  proof: rfl

中文:
引理 coe_posPart
  条件: (f : α ->ᵇ β)
  结论: ⇑f⁺ = (⇑f)⁺
  证明: rfl
-/
@[simp, norm_cast] lemma coe_posPart (f : α ->ᵇ β) : ⇑f⁺ = (⇑f)⁺ := rfl
/--
lemma `coe_negPart` / 引理 `coe_negPart`

English:
lemma coe_negPart
  given: (f : α ->ᵇ β)
  statement: ⇑f⁻ = (⇑f)⁻
  proof: rfl

中文:
引理 coe_negPart
  条件: (f : α ->ᵇ β)
  结论: ⇑f⁻ = (⇑f)⁻
  证明: rfl
-/
@[simp, norm_cast] lemma coe_negPart (f : α ->ᵇ β) : ⇑f⁻ = (⇑f)⁻ := rfl

/--
Instance `instHasSolidNorm` / 实例 `instHasSolidNorm`

English:
instance instHasSolidNorm
  signature: : HasSolidNorm (α ->ᵇ β)
  body: { solid := by
      intro f g h
      have i1 : forall t, ‖f t‖ <= ‖g t‖ := fun t => HasSolidNorm.solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }

中文:
实例 instHasSolidNorm
  签名: : 有Solid范数 (α ->ᵇ β)
  定义体: { solid := by
      intro f g h
      have i1 : forall t, ‖f t‖ <= ‖g t‖ := fun t => HasSolidNorm.solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }

Depends on / 依赖: HasSolidNorm, HasSolidNorm.solid, norm_coe_le_norm, norm_le, norm_nonneg
-/
instance instHasSolidNorm : HasSolidNorm (α ->ᵇ β) :=
  { solid := by
      intro f g h
      have i1 : forall t, ‖f t‖ <= ‖g t‖ := fun t => HasSolidNorm.solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid (α ->ᵇ β) where
  body: by simpa using h₁ _

中文:
实例 instIsOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 (α ->ᵇ β) where
  定义体: by simpa using h₁ _
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (α ->ᵇ β) where
  add_le_add_left f g h₁ h t := by simpa using h₁ _

end NormedLatticeOrderedGroup

section NonnegativePart

variable [TopologicalSpace α]

/--
Definition of `nnrealPart` / `nnrealPart` 的定义

English:
definition nnrealPart
  signature: (f : α ->ᵇ Real)
  body: BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f

@[simp]

中文:
定义 nnrealPart
  签名: (f : α ->ᵇ 实数)
  定义体: BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.comp, LipschitzWith, Real.toNNReal, lipschitzWith_posPart, toNNReal
-/
def nnrealPart (f : α ->ᵇ Real) : α ->ᵇ Real>=0 :=
  BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f

@[simp]
/--
theorem `nnrealPart_coeFn_eq` / 定理 `nnrealPart_coeFn_eq`

English:
theorem nnrealPart_coeFn_eq
  given: (f : α ->ᵇ Real)
  statement: ⇑f.nnrealPart = Real.toNNReal ∘ ⇑f
  proof: rfl

中文:
定理 nnrealPart_coeFn_eq
  条件: (f : α ->ᵇ 实数)
  结论: ⇑f.nnrealPart = 实数.toNN实数 ∘ ⇑f
  证明: rfl
-/
theorem nnrealPart_coeFn_eq (f : α ->ᵇ Real) : ⇑f.nnrealPart = Real.toNNReal ∘ ⇑f := rfl

/--
Definition of `nnnorm` / `nnnorm` 的定义

English:
definition nnnorm
  signature: (f : α ->ᵇ Real)
  body: BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : Real => ‖x‖₊ from lipschitzWith_one_norm) f

@[simp]

中文:
定义 nnnorm
  签名: (f : α ->ᵇ 实数)
  定义体: BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : Real => ‖x‖₊ from lipschitzWith_one_norm) f

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.comp, LipschitzWith, lipschitzWith_one_norm
-/
def nnnorm (f : α ->ᵇ Real) : α ->ᵇ Real>=0 :=
  BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : Real => ‖x‖₊ from lipschitzWith_one_norm) f

@[simp]
/--
theorem `nnnorm_coeFn_eq` / 定理 `nnnorm_coeFn_eq`

English:
theorem nnnorm_coeFn_eq
  given: (f : α ->ᵇ Real)
  statement: ⇑f.nnnorm = NNNorm.nnnorm ∘ ⇑f
  proof: rfl

中文:
定理 nnnorm_coeFn_eq
  条件: (f : α ->ᵇ 实数)
  结论: ⇑f.nnnorm = NN范数.nnnorm ∘ ⇑f
  证明: rfl
-/
theorem nnnorm_coeFn_eq (f : α ->ᵇ Real) : ⇑f.nnnorm = NNNorm.nnnorm ∘ ⇑f := rfl

-- TODO: Use `posPart` and `negPart` here
/--
theorem `self_eq_nnrealPart_sub_nnrealPart_neg` / 定理 `self_eq_nnrealPart_sub_nnrealPart_neg`

English:
theorem self_eq_nnrealPart_sub_nnrealPart_neg
  given: (f : α ->ᵇ Real)
  proof: by
  funext x
  dsimp
  simp only [max_zero_sub_max_neg_zero_eq_self]

中文:
定理 self_eq_nnrealPart_sub_nnrealPart_neg
  条件: (f : α ->ᵇ 实数)
  证明: by
  funext x
  dsimp
  simp only [max_zero_sub_max_neg_zero_eq_self]

Depends on / 依赖: max_zero_sub_max_neg_zero_eq_self
-/
theorem self_eq_nnrealPart_sub_nnrealPart_neg (f : α ->ᵇ Real) :
    ⇑f = (↑) ∘ f.nnrealPart - (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_sub_max_neg_zero_eq_self]

/--
theorem `abs_self_eq_nnrealPart_add_nnrealPart_neg` / 定理 `abs_self_eq_nnrealPart_add_nnrealPart_neg`

English:
theorem abs_self_eq_nnrealPart_add_nnrealPart_neg
  given: (f : α ->ᵇ Real)
  proof: by
  funext x
  dsimp
  simp only [max_zero_add_max_neg_zero_eq_abs_self]

中文:
定理 abs_self_eq_nnrealPart_add_nnrealPart_neg
  条件: (f : α ->ᵇ 实数)
  证明: by
  funext x
  dsimp
  simp only [max_zero_add_max_neg_zero_eq_abs_self]

Depends on / 依赖: max_zero_add_max_neg_zero_eq_abs_self
-/
theorem abs_self_eq_nnrealPart_add_nnrealPart_neg (f : α ->ᵇ Real) :
    abs ∘ ⇑f = (↑) ∘ f.nnrealPart + (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_add_max_neg_zero_eq_abs_self]

end NonnegativePart

section

variable {α : Type*} [TopologicalSpace α]

-- TODO: `f + const _ ‖f‖` is just `f⁺`
/--
lemma `add_norm_nonneg` / 引理 `add_norm_nonneg`

English:
lemma add_norm_nonneg
  given: (f : α ->ᵇ Real)
  proof: by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_add,
    const_apply, Pi.add_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

中文:
引理 add_norm_nonneg
  条件: (f : α ->ᵇ 实数)
  证明: by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_add,
    const_apply, Pi.add_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

Depends on / 依赖: ContinuousMap, ContinuousMap.toFun_eq_coe, Pi.add_apply, Pi.zero_apply, abs_le, abs_le.mp, add_apply, coe_add, coe_toContinuousMap, coe_zero, const_apply, norm_coe_le_norm, toFun_eq_coe, zero_apply
-/
lemma add_norm_nonneg (f : α ->ᵇ Real) :
    0 <= f + const _ ‖f‖ := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_add,
    const_apply, Pi.add_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

/--
lemma `norm_sub_nonneg` / 引理 `norm_sub_nonneg`

English:
lemma norm_sub_nonneg
  given: (f : α ->ᵇ Real)
  proof: by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_sub,
    const_apply, Pi.sub_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

中文:
引理 norm_sub_nonneg
  条件: (f : α ->ᵇ 实数)
  证明: by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_sub,
    const_apply, Pi.sub_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

Depends on / 依赖: ContinuousMap, ContinuousMap.toFun_eq_coe, Pi.sub_apply, Pi.zero_apply, abs_le, abs_le.mp, coe_sub, coe_toContinuousMap, coe_zero, const_apply, norm_coe_le_norm, sub_apply, toFun_eq_coe, zero_apply
-/
lemma norm_sub_nonneg (f : α ->ᵇ Real) :
    0 <= const _ ‖f‖ - f := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_sub,
    const_apply, Pi.sub_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

end

end BoundedContinuousFunction
