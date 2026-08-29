/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.OfFun

/-!
# Extended metric spaces

This file is devoted to the definition and study of `EMetricSpace`s, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `EMetricSpace` therefore extends `UniformSpace` (and `TopologicalSpace`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `PseudoEMetricSpace`, where we don't require `edist x y = 0 → x = y` and we specialize
to `EMetricSpace` at the end.
-/

@[expose] public section


assert_not_exists Nat.instLocallyFiniteOrder IsUniformEmbedding.prod TendstoUniformlyOnFilter

open Filter Set Topology Set.Notation

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

/--
theorem `uniformity_dist_of_mem_uniformity` / 定理 `uniformity_dist_of_mem_uniformity`

English:
theorem uniformity_dist_of_mem_uniformity
  statement: [LT β] {U : Filter (α × α)} (z : β)
  proof: HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_ofPred]⟩

中文:
定理 uniformity_dist_of_mem_uniformity
  结论: [LT β] {U : 滤子 (α × α)} (z : β)
  证明: HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_ofPred]⟩

Depends on / 依赖: HasBasis, HasBasis.eq_biInf, Prod.forall, eq_biInf, mem_ofPred, subset_def
-/
theorem uniformity_dist_of_mem_uniformity [LT β] {U : Filter (α × α)} (z : β)
    (D : α -> α -> β) (H : forall s, s in U ↔ exists ε > z, forall {a b : α}, D a b < ε -> (a, b) in s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_ofPred]⟩

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

/-- `EDist α` means that `α` is equipped with an extended distance. -/
@[ext]
/--
Definition of `EDist` / `EDist` 的定义

English:
class EDist
  parameters: (α : Type*)
  axioms and operations (1):
    - edist : α -> α -> Real>=0∞

中文:
类 EDist
  参数: (α : 类型)
  公理与运算 (1 个):
    - edist : α -> α -> 实数>=0∞
-/
class EDist (α : Type*) where
  /-- Extended distance between two points -/
  edist : α -> α -> Real>=0∞

export EDist (edist)

section

variable {x y z : α} {ε : Real>=0∞} [EDist α]

/--
Definition of `Metric.eball` / `Metric.eball` 的定义

English:
definition Metric.eball
  signature: (x : α) (ε : Real>=0∞)
  body: { y | edist y x < ε }

中文:
定义 Metric.eball
  签名: (x : α) (ε : 实数>=0∞)
  定义体: { y | edist y x < ε }
-/
def Metric.eball (x : α) (ε : Real>=0∞) : Set α :=
  { y | edist y x < ε }

/--
theorem `Metric.mem_eball` / 定理 `Metric.mem_eball`

English:
theorem Metric.mem_eball
  given: {x y : α} {ε : Real>=0∞}
  statement: y in eball x ε ↔ edist y x < ε
  proof: Iff.rfl

中文:
定理 Metric.mem_eball
  条件: {x y : α} {ε : 实数>=0∞}
  结论: y in eball x ε ↔ edist y x < ε
  证明: Iff.rfl
-/
@[simp] theorem Metric.mem_eball {x y : α} {ε : Real>=0∞} : y in eball x ε ↔ edist y x < ε := Iff.rfl

end

/-- Creating a uniform space from an extended distance. -/
@[reducible]
/--
Definition of `uniformSpaceOfEDist` / `uniformSpaceOfEDist` 的定义

English:
definition uniformSpaceOfEDist
  signature: (edist : α -> α -> Real>=0∞) (edist_self : forall x : α, edist x x = 0)
  body: .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

中文:
定义 uniformSpaceOfEDist
  签名: (edist : α -> α -> 实数>=0∞) (edist_self : 对任意 x : α, edist x x = 0)
  定义体: .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

Depends on / 依赖: ENNReal, ENNReal.add_halves, ENNReal.add_lt_add, ENNReal.half_pos, add_halves, add_lt_add, edist_comm, edist_self, edist_triangle, half_pos, trans_eq
-/
noncomputable def uniformSpaceOfEDist (edist : α -> α -> Real>=0∞) (edist_self : forall x : α, edist x x = 0)
    (edist_comm : forall x y : α, edist x y = edist y x)
    (edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z) : UniformSpace α :=
  .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

/--
Definition of `uniformSpaceOfEDistOfHasBasis` / `uniformSpaceOfEDistOfHasBasis` 的定义

English:
definition uniformSpaceOfEDistOfHasBasis
  signature: [TopologicalSpace α]
  body: .ofFunOfHasBasis edist edist_self edist_comm edist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis

中文:
定义 uniformSpaceOfEDistOfHasBasis
  签名: [拓扑空间 α]
  定义体: .ofFunOfHasBasis edist edist_self edist_comm edist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis
-/
@[reducible] noncomputable def uniformSpaceOfEDistOfHasBasis [TopologicalSpace α]
    (edist : α -> α -> Real>=0∞)
    (edist_self : forall x : α, edist x x = 0)
    (edist_comm : forall x y : α, edist x y = edist y x)
    (edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z)
    (basis : forall x, (𝓝 x).HasBasis (fun c => 0 < c) (fun c => {y | edist x y < c})) :
    UniformSpace α :=
  .ofFunOfHasBasis edist edist_self edist_comm edist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis

/--
Definition of `PseudoEMetricSpace` / `PseudoEMetricSpace` 的定义

English:
class PseudoEMetricSpace
  parameters: (α : Type u)
  extends: EDist α
  axioms and operations (5):
    - edist_self : forall x : α, edist x x = 0
    - edist_comm : forall x y : α, edist x y = edist y x
    - edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z
    - toUniformSpace : UniformSpace α  [default: uniformSpaceOfEDist edist edist_self edist_comm edist_triang]
    - uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }  [default: by rfl]

中文:
类 PseudoEMetric空间
  参数: (α : 类型u)
  继承: EDist α
  公理与运算 (5 个):
    - edist_self : 对任意 x : α, edist x x = 0
    - edist_comm : 对任意 x y : α, edist x y = edist y x
    - edist_triangle : 对任意 x y z : α, edist x z <= edist x y + edist y z
    - toUniformSpace : 一致空间 α  [默认: uniformSpaceOfEDist edist edist_self edist_comm edist_triang]
    - uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }  [默认: by rfl]

Depends on / 依赖: edist_comm, edist_self, edist_triangle, uniformSpaceOfEDist
-/
class PseudoEMetricSpace (α : Type u) : Type u extends EDist α where
  edist_self : forall x : α, edist x x = 0
  edist_comm : forall x y : α, edist x y = edist y x
  edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by rfl

attribute [instance_reducible, instance] PseudoEMetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/

/-- Two pseudo emetric space structures with the same edistance function coincide. -/
@[ext]
/--
theorem `PseudoEMetricSpace.ext` / 定理 `PseudoEMetricSpace.ext`

English:
theorem PseudoEMetricSpace.ext
  statement: {α : Type*} {m m' : PseudoEMetricSpace α}
  proof: by
  obtain ⟨_, _, _, U, hU⟩ := m; rename EDist α => ed
  obtain ⟨_, _, _, U', hU'⟩ := m'; rename EDist α => ed'
  congr 1
  exact UniformSpace.ext (((show ed = ed' from h) ▸ hU).trans hU'.symm)

中文:
定理 PseudoEMetric空间.ext
  结论: {α : 类型} {m m' : PseudoEMetric空间 α}
  证明: by
  obtain ⟨_, _, _, U, hU⟩ := m; rename EDist α => ed
  obtain ⟨_, _, _, U', hU'⟩ := m'; rename EDist α => ed'
  congr 1
  exact UniformSpace.ext (((show ed = ed' from h) ▸ hU).trans hU'.symm)
-/
protected theorem PseudoEMetricSpace.ext {α : Type*} {m m' : PseudoEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  obtain ⟨_, _, _, U, hU⟩ := m; rename EDist α => ed
  obtain ⟨_, _, _, U', hU'⟩ := m'; rename EDist α => ed'
  congr 1
  exact UniformSpace.ext (((show ed = ed' from h) ▸ hU).trans hU'.symm)

variable [PseudoEMetricSpace α]

export PseudoEMetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/--
theorem `edist_triangle_left` / 定理 `edist_triangle_left`

English:
theorem edist_triangle_left
  given: (x y z : α)
  statement: edist x y <= edist z x + edist z y
  proof: by
  rw [edist_comm z]; apply edist_triangle

中文:
定理 edist_triangle_left
  条件: (x y z : α)
  结论: edist x y <= edist z x + edist z y
  证明: by
  rw [edist_comm z]; apply edist_triangle

Depends on / 依赖: edist_comm, edist_triangle
-/
theorem edist_triangle_left (x y z : α) : edist x y <= edist z x + edist z y := by
  rw [edist_comm z]; apply edist_triangle

/--
theorem `edist_triangle_right` / 定理 `edist_triangle_right`

English:
theorem edist_triangle_right
  given: (x y z : α)
  statement: edist x y <= edist x z + edist y z
  proof: by
  rw [edist_comm y]; apply edist_triangle

中文:
定理 edist_triangle_right
  条件: (x y z : α)
  结论: edist x y <= edist x z + edist y z
  证明: by
  rw [edist_comm y]; apply edist_triangle

Depends on / 依赖: edist_comm, edist_triangle
-/
theorem edist_triangle_right (x y z : α) : edist x y <= edist x z + edist y z := by
  rw [edist_comm y]; apply edist_triangle

/--
theorem `edist_congr_right` / 定理 `edist_congr_right`

English:
theorem edist_congr_right
  given: {x y z : α} (h : edist x y = 0)
  statement: edist x z = edist y z
  proof: by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z)]; rw [← h]
    apply edist_triangle

中文:
定理 edist_congr_right
  条件: {x y z : α} (h : edist x y = 0)
  结论: edist x z = edist y z
  证明: by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z)]; rw [← h]
    apply edist_triangle

Depends on / 依赖: edist_comm, edist_triangle, le_antisymm, zero_add
-/
theorem edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z := by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z)]; rw [← h]
    apply edist_triangle

/--
theorem `edist_congr_left` / 定理 `edist_congr_left`

English:
theorem edist_congr_left
  given: {x y z : α} (h : edist x y = 0)
  statement: edist z x = edist z y
  proof: by
  rw [edist_comm z x]; rw [edist_comm z y]
  apply edist_congr_right h

中文:
定理 edist_congr_left
  条件: {x y z : α} (h : edist x y = 0)
  结论: edist z x = edist z y
  证明: by
  rw [edist_comm z x]; rw [edist_comm z y]
  apply edist_congr_right h

Depends on / 依赖: edist_comm, edist_congr_right
-/
theorem edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y := by
  rw [edist_comm z x]; rw [edist_comm z y]
  apply edist_congr_right h

/--
theorem `edist_congr` / 定理 `edist_congr`

English:
theorem edist_congr
  given: {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0)
  proof: (edist_congr_right hl).trans (edist_congr_left hr)

中文:
定理 edist_congr
  条件: {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0)
  证明: (edist_congr_right hl).trans (edist_congr_left hr)

Depends on / 依赖: edist_congr_left, edist_congr_right
-/
theorem edist_congr {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0) :
    edist w y = edist x z :=
  (edist_congr_right hl).trans (edist_congr_left hr)

/--
theorem `edist_triangle4` / 定理 `edist_triangle4`

English:
theorem edist_triangle4
  given: (x y z t : α)
  statement: edist x t <= edist x y + edist y z + edist z t
  proof: by
  grw [edist_triangle _ z, edist_triangle]

中文:
定理 edist_triangle4
  条件: (x y z t : α)
  结论: edist x t <= edist x y + edist y z + edist z t
  证明: by
  grw [edist_triangle _ z, edist_triangle]

Depends on / 依赖: edist_triangle
-/
theorem edist_triangle4 (x y z t : α) : edist x t <= edist x y + edist y z + edist z t := by
  grw [edist_triangle _ z, edist_triangle]

/--
theorem `uniformity_pseudoedist` / 定理 `uniformity_pseudoedist`

English:
theorem uniformity_pseudoedist
  statement: 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }
  proof: PseudoEMetricSpace.uniformity_edist

中文:
定理 uniformity_pseudoedist
  结论: 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }
  证明: PseudoEMetricSpace.uniformity_edist

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.uniformity_edist, uniformity_edist
-/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist

/--
theorem `uniformSpace_edist` / 定理 `uniformSpace_edist`

English:
theorem uniformSpace_edist
  proof: UniformSpace.ext uniformity_pseudoedist

中文:
定理 uniformSpace_edist
  证明: UniformSpace.ext uniformity_pseudoedist

Depends on / 依赖: UniformSpace, UniformSpace.ext, uniformity_pseudoedist
-/
theorem uniformSpace_edist :
    ‹PseudoEMetricSpace α›.toUniformSpace =
      uniformSpaceOfEDist edist edist_self edist_comm edist_triangle :=
  UniformSpace.ext uniformity_pseudoedist

/--
theorem `uniformity_basis_edist` / 定理 `uniformity_basis_edist`

English:
theorem uniformity_basis_edist
  proof: (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

中文:
定理 uniformity_basis_edist
  证明: (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_ofFun, hasBasis_ofFun, one_pos, uniformSpace_edist
-/
theorem uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

/--
theorem `mem_uniformity_edist` / 定理 `mem_uniformity_edist`

English:
theorem mem_uniformity_edist
  given: {s : Set (α × α)}
  proof: uniformity_basis_edist.mem_uniformity_iff

中文:
定理 mem_uniformity_edist
  条件: {s : 集合 (α × α)}
  证明: uniformity_basis_edist.mem_uniformity_iff

Depends on / 依赖: mem_uniformity_iff, uniformity_basis_edist, uniformity_basis_edist.mem_uniformity_iff
-/
theorem mem_uniformity_edist {s : Set (α × α)} :
    s in 𝓤 α ↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s :=
  uniformity_basis_edist.mem_uniformity_iff

/--
Definition of `PseudoEMetricSpace.ofEDist` / `PseudoEMetricSpace.ofEDist` 的定义

English:
abbreviation PseudoEMetricSpace.ofEDist
  body: edist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist := by rfl

中文:
缩写 PseudoEMetric空间.ofEDist
  定义体: edist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist := by rfl
-/
noncomputable abbrev PseudoEMetricSpace.ofEDist
    {α : Type u} (edist : α -> α -> Real>=0∞) (edist_self : forall x : α, edist x x = 0)
    (edist_comm : forall x y : α, edist x y = edist y x) (edist_triangle : forall x y z :
    α, edist x z <= edist x y + edist y z) : PseudoEMetricSpace α where
  edist := edist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist := by rfl

/--
theorem `EMetric.toUniformSpace_ofEDist` / 定理 `EMetric.toUniformSpace_ofEDist`

English:
theorem EMetric.toUniformSpace_ofEDist
  statement: {α : Type u} [EDist α] (edist_self : forall x : α, edist x x = 0)
  proof: by rfl

中文:
定理 EMetric.toUniformSpace_ofEDist
  结论: {α : 类型u} [EDist α] (edist_self : 对任意 x : α, edist x x = 0)
  证明: by rfl
-/
theorem EMetric.toUniformSpace_ofEDist {α : Type u} [EDist α] (edist_self : forall x : α, edist x x = 0)
    (edist_comm : forall x y : α, edist x y = edist y x)
    (edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z) :
    (PseudoEMetricSpace.ofEDist edist edist_self edist_comm edist_triangle).toUniformSpace =
      (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle) := by rfl

/--
theorem `EMetric.mk_uniformity_basis` / 定理 `EMetric.mk_uniformity_basis`

English:
theorem EMetric.mk_uniformity_basis
  statement: {β : Type*} {p : β -> Prop} {f : β -> Real>=0∞}
  proof: by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

中文:
定理 EMetric.mk_uniformity_basis
  结论: {β : 类型} {p : β -> 命题} {f : β -> 实数>=0∞}
  证明: by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
-/
protected theorem EMetric.mk_uniformity_basis {β : Type*} {p : β -> Prop} {f : β -> Real>=0∞}
    (hf₀ : forall x, p x -> 0 < f x) (hf : forall ε, 0 < ε -> exists x, p x ∧ f x <= ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/--
theorem `EMetric.mk_uniformity_basis_le` / 定理 `EMetric.mk_uniformity_basis_le`

English:
theorem EMetric.mk_uniformity_basis_le
  statement: {β : Type*} {p : β -> Prop} {f : β -> Real>=0∞}
  proof: by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fu

中文:
定理 EMetric.mk_uniformity_basis_le
  结论: {β : 类型} {p : β -> 命题} {f : β -> 实数>=0∞}
  证明: by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fu
-/
protected theorem EMetric.mk_uniformity_basis_le {β : Type*} {p : β -> Prop} {f : β -> Real>=0∞}
    (hf₀ : forall x, p x -> 0 < f x) (hf : forall ε, 0 < ε -> exists x, p x ∧ f x <= ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 <= f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x hx => hε lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx.out)⟩

/--
theorem `uniformity_basis_edist_le` / 定理 `uniformity_basis_edist_le`

English:
theorem uniformity_basis_edist_le
  proof: EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

中文:
定理 uniformity_basis_edist_le
  证明: EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis_le, le_refl, mk_uniformity_basis_le
-/
theorem uniformity_basis_edist_le :
    (𝓤 α).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 <= ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

/--
theorem `uniformity_basis_edist'` / 定理 `uniformity_basis_edist'`

English:
theorem uniformity_basis_edist'
  given: (ε' : Real>=0∞) (hε' : 0 < ε')
  proof: EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

中文:
定理 uniformity_basis_edist'
  条件: (ε' : 实数>=0∞) (hε' : 0 < ε')
  证明: EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

Depends on / 依赖: And.left, EMetric, EMetric.mk_uniformity_basis, exists_between, lt_min, lt_of_le_of_lt, min_le_left, min_le_right, mk_uniformity_basis
-/
theorem uniformity_basis_edist' (ε' : Real>=0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : Real>=0∞ => ε in Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

/--
theorem `uniformity_basis_edist_le'` / 定理 `uniformity_basis_edist_le'`

English:
theorem uniformity_basis_edist_le'
  given: (ε' : Real>=0∞) (hε' : 0 < ε')
  proof: EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

中文:
定理 uniformity_basis_edist_le'
  条件: (ε' : 实数>=0∞) (hε' : 0 < ε')
  证明: EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

Depends on / 依赖: And.left, EMetric, EMetric.mk_uniformity_basis_le, exists_between, lt_min, lt_of_le_of_lt, min_le_left, min_le_right, mk_uniformity_basis_le
-/
theorem uniformity_basis_edist_le' (ε' : Real>=0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : Real>=0∞ => ε in Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 <= ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

/--
theorem `uniformity_basis_edist_nnreal` / 定理 `uniformity_basis_edist_nnreal`

English:
theorem uniformity_basis_edist_nnreal
  proof: EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

中文:
定理 uniformity_basis_edist_nnreal
  证明: EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis, ENNReal, ENNReal.coe_pos, ENNReal.lt_iff_exists_nnreal_btwn, coe_pos, le_of_lt, lt_iff_exists_nnreal_btwn, mk_uniformity_basis
-/
theorem uniformity_basis_edist_nnreal :
    (𝓤 α).HasBasis (fun ε : Real>=0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

/--
theorem `uniformity_basis_edist_nnreal_le` / 定理 `uniformity_basis_edist_nnreal_le`

English:
theorem uniformity_basis_edist_nnreal_le
  proof: EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

中文:
定理 uniformity_basis_edist_nnreal_le
  证明: EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis_le, ENNReal, ENNReal.coe_pos, ENNReal.lt_iff_exists_nnreal_btwn, coe_pos, le_of_lt, lt_iff_exists_nnreal_btwn, mk_uniformity_basis_le
-/
theorem uniformity_basis_edist_nnreal_le :
    (𝓤 α).HasBasis (fun ε : Real>=0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 <= ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

/--
theorem `uniformity_basis_edist_inv_nat` / 定理 `uniformity_basis_edist_inv_nat`

English:
theorem uniformity_basis_edist_inv_nat
  proof: EMetric.mk_uniformity_basis (fun n _ => ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

中文:
定理 uniformity_basis_edist_inv_nat
  证明: EMetric.mk_uniformity_basis (fun n _ => ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis, ENNReal, ENNReal.exists_inv_nat_lt, ENNReal.inv_pos, ENNReal.natCast_ne_top, exists_inv_nat_lt, inv_pos, le_of_lt, mk_uniformity_basis, natCast_ne_top, ne_of_gt
-/
theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  EMetric.mk_uniformity_basis (fun n _ => ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

/--
theorem `uniformity_basis_edist_inv_two_pow` / 定理 `uniformity_basis_edist_inv_two_pow`

English:
theorem uniformity_basis_edist_inv_two_pow
  proof: EMetric.mk_uniformity_basis (fun _ _ => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

中文:
定理 uniformity_basis_edist_inv_two_pow
  证明: EMetric.mk_uniformity_basis (fun _ _ => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis, ENNReal, ENNReal.exists_inv_two_pow_lt, ENNReal.inv_pos, ENNReal.ofNat_ne_top, ENNReal.pow_pos, exists_inv_two_pow_lt, inv_pos, le_of_lt, mk_uniformity_basis, ne_of_gt, ofNat_ne_top, pow_pos
-/
theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  EMetric.mk_uniformity_basis (fun _ _ => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

/--
theorem `edist_mem_uniformity` / 定理 `edist_mem_uniformity`

English:
theorem edist_mem_uniformity
  given: {ε : Real>=0∞} (ε0 : 0 < ε)
  statement: { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
  proof: mem_uniformity_edist.2 ⟨ε, ε0, id⟩

中文:
定理 edist_mem_uniformity
  条件: {ε : 实数>=0∞} (ε0 : 0 < ε)
  结论: { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
  证明: mem_uniformity_edist.2 ⟨ε, ε0, id⟩

Depends on / 依赖: mem_uniformity_edist
-/
theorem edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } in 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, id⟩

namespace EMetric

instance (priority := 900) instIsCountablyGeneratedUniformity : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_iInf⟩

/--
theorem `uniformContinuousOn_iff` / 定理 `uniformContinuousOn_iff`

English:
theorem uniformContinuousOn_iff
  given: [PseudoEMetricSpace β] {f : α -> β} {s : Set α}
  proof: uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist

中文:
定理 uniformContinuousOn_iff
  条件: [PseudoEMetric空间 β] {f : α -> β} {s : 集合 α}
  证明: uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist

Depends on / 依赖: uniformContinuousOn_iff, uniformity_basis_edist, uniformity_basis_edist.uniformContinuousOn_iff
-/
theorem uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α -> β} {s : Set α} :
    UniformContinuousOn f s ↔
      forall ε > 0, exists δ > 0, forall {a}, a in s -> forall {b}, b in s -> edist a b < δ -> edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist

/--
theorem `uniformContinuous_iff` / 定理 `uniformContinuous_iff`

English:
theorem uniformContinuous_iff
  given: [PseudoEMetricSpace β] {f : α -> β}
  proof: uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist

中文:
定理 uniformContinuous_iff
  条件: [PseudoEMetric空间 β] {f : α -> β}
  证明: uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist

Depends on / 依赖: uniformContinuous_iff, uniformity_basis_edist, uniformity_basis_edist.uniformContinuous_iff
-/
theorem uniformContinuous_iff [PseudoEMetricSpace β] {f : α -> β} :
    UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall {a b : α}, edist a b < δ -> edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist

end EMetric

open EMetric

/--
Definition of `PseudoEMetricSpace.replaceUniformity` / `PseudoEMetricSpace.replaceUniformity` 的定义

English:
abbreviation PseudoEMetricSpace.replaceUniformity
  signature: {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
  body: @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)

中文:
缩写 PseudoEMetric空间.replaceUniformity
  签名: {α} [U : 一致空间 α] (m : PseudoEMetric空间 α)
  定义体: @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)

Depends on / 依赖: m.toEDist, toEDist
-/
abbrev PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetricSpace α where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)

/--
Definition of `PseudoEMetricSpace.induced` / `PseudoEMetricSpace.induced` 的定义

English:
abbreviation PseudoEMetricSpace.induced
  signature: {α β} (f : α -> β) (m : PseudoEMetricSpace β)
  body: edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf

中文:
缩写 PseudoEMetric空间.induced
  签名: {α β} (f : α -> β) (m : PseudoEMetric空间 β)
  定义体: edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf
-/
abbrev PseudoEMetricSpace.induced {α β} (f : α -> β) (m : PseudoEMetricSpace β) :
    PseudoEMetricSpace α where
  edist x y := edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type*} {p : α -> Prop} [PseudoEMetricSpace α] : PseudoEMetricSpace (Subtype p) :=
  PseudoEMetricSpace.induced Subtype.val ‹_›

/--
theorem `Subtype.edist_eq` / 定理 `Subtype.edist_eq`

English:
theorem Subtype.edist_eq
  given: {p : α -> Prop} (x y : Subtype p)
  statement: edist x y = edist (x : α) y
  proof: rfl

中文:
定理 子类型.edist_eq
  条件: {p : α -> 命题} (x y : 子类型 p)
  结论: edist x y = edist (x : α) y
  证明: rfl
-/
theorem Subtype.edist_eq {p : α -> Prop} (x y : Subtype p) : edist x y = edist (x : α) y := rfl

/-- The extended pseudodistance on a subtype of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
@[simp]
/--
theorem `Subtype.edist_mk_mk` / 定理 `Subtype.edist_mk_mk`

English:
theorem Subtype.edist_mk_mk
  given: {p : α -> Prop} {x y : α} (hx : p x) (hy : p y)
  proof: rfl

中文:
定理 子类型.edist_mk_mk
  条件: {p : α -> 命题} {x y : α} (hx : p x) (hy : p y)
  证明: rfl
-/
theorem Subtype.edist_mk_mk {p : α -> Prop} {x y : α} (hx : p x) (hy : p y) :
    edist (⟨x, hx⟩ : Subtype p) ⟨y, hy⟩ = edist x y :=
  rfl

/--
Definition of `PseudoEMetricSpace.ofEDistOfTopology` / `PseudoEMetricSpace.ofEDistOfTopology` 的定义

English:
definition PseudoEMetricSpace.ofEDistOfTopology
  signature: {α : Type*} [TopologicalSpace α]
  body: d
  edist_self := h_self
  edist_comm := h_comm
  edist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_edist := rfl

@[deprecated (since := "2026-01-08")]
alias PseudoEmetricSpace.ofEdistOfTopology := PseudoEMetricSpace.ofEDis

中文:
定义 PseudoEMetric空间.ofEDistOfTopology
  签名: {α : 类型} [拓扑空间 α]
  定义体: d
  edist_self := h_self
  edist_comm := h_comm
  edist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_edist := rfl

@[deprecated (since := "2026-01-08")]
alias PseudoEmetricSpace.ofEdistOfTopology := PseudoEMetricSpace.ofEDis
-/
@[reducible] noncomputable def PseudoEMetricSpace.ofEDistOfTopology {α : Type*} [TopologicalSpace α]
    (d : α -> α -> Real>=0∞) (h_self : forall x, d x x = 0) (h_comm : forall x y, d x y = d y x)
    (h_triangle : forall x y z, d x z <= d x y + d y z)
    (h_basis : forall x, (𝓝 x).HasBasis (fun c => 0 < c) (fun c => {y | d x y < c})) :
    PseudoEMetricSpace α where
  edist := d
  edist_self := h_self
  edist_comm := h_comm
  edist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_edist := rfl

@[deprecated (since := "2026-01-08")]
alias PseudoEmetricSpace.ofEdistOfTopology := PseudoEMetricSpace.ofEDistOfTopology

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive
/-- Pseudoemetric space instance on the additive opposite of a pseudoemetric space. -/]
instance {α : Type*} [PseudoEMetricSpace α] : PseudoEMetricSpace αᵐᵒᵖ :=
  PseudoEMetricSpace.induced unop ‹_›

@[to_additive]
/--
theorem `edist_unop` / 定理 `edist_unop`

English:
theorem edist_unop
  given: (x y : αᵐᵒᵖ)
  statement: edist (unop x) (unop y) = edist x y
  proof: rfl

@[to_additive]

中文:
定理 edist_unop
  条件: (x y : αᵐᵒᵖ)
  结论: edist (unop x) (unop y) = edist x y
  证明: rfl

@[to_additive]
-/
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y := rfl

@[to_additive]
/--
theorem `edist_op` / 定理 `edist_op`

English:
theorem edist_op
  given: (x y : α)
  statement: edist (op x) (op y) = edist x y
  proof: rfl

中文:
定理 edist_op
  条件: (x y : α)
  结论: edist (op x) (op y) = edist x y
  证明: rfl
-/
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y := rfl

end MulOpposite

section ULift

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (ULift α)
  body: PseudoEMetricSpace.induced ULift.down ‹_›

中文:
实例 :
  签名: PseudoEMetric空间 (类型层提升 α)
  定义体: PseudoEMetricSpace.induced ULift.down ‹_›

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.induced, ULift.down, induced
-/
instance : PseudoEMetricSpace (ULift α) := PseudoEMetricSpace.induced ULift.down ‹_›

/--
theorem `ULift.edist_eq` / 定理 `ULift.edist_eq`

English:
theorem ULift.edist_eq
  given: (x y : ULift α)
  statement: edist x y = edist x.down y.down
  proof: rfl

@[simp]

中文:
定理 类型层提升.edist_eq
  条件: (x y : 类型层提升 α)
  结论: edist x y = edist x.down y.down
  证明: rfl

@[simp]
-/
theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down := rfl

@[simp]
/--
theorem `ULift.edist_up_up` / 定理 `ULift.edist_up_up`

English:
theorem ULift.edist_up_up
  given: (x y : α)
  statement: edist (ULift.up x) (ULift.up y) = edist x y
  proof: rfl

中文:
定理 类型层提升.edist_up_up
  条件: (x y : α)
  结论: edist (类型层提升.up x) (类型层提升.up y) = edist x y
  证明: rfl
-/
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y := rfl

end ULift

/--
Instance `Prod.pseudoEMetricSpaceMax` / 实例 `Prod.pseudoEMetricSpaceMax`

English:
instance Prod.pseudoEMetricSpaceMax
  signature: [PseudoEMetricSpace β]
  body: edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle _ _ _ :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right

中文:
实例 积类型.pseudoEMetricSpaceMax
  签名: [PseudoEMetric空间 β]
  定义体: edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle _ _ _ :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right
-/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] :
    PseudoEMetricSpace (α × β) where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle _ _ _ :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
uniformity_edist := uniformity_prod.trans by
    simp [PseudoEMetricSpace.uniformity_edist, ← iInf_inf_eq, ofPred_and]
  toUniformSpace := inferInstance

/--
theorem `Prod.edist_eq` / 定理 `Prod.edist_eq`

English:
theorem Prod.edist_eq
  given: [PseudoEMetricSpace β] (x y : α × β)
  proof: rfl

中文:
定理 积类型.edist_eq
  条件: [PseudoEMetric空间 β] (x y : α × β)
  证明: rfl
-/
theorem Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) :
    edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : Real>=0∞} {s t : Set α}

/--
theorem `mem_eball'` / 定理 `mem_eball'`

English:
theorem mem_eball'
  statement: y in eball x ε ↔ edist x y < ε
  proof: by rw [edist_comm, mem_eball]

中文:
定理 mem_eball'
  结论: y in eball x ε ↔ edist x y < ε
  证明: by rw [edist_comm, mem_eball]

Depends on / 依赖: edist_comm, mem_eball
-/
theorem mem_eball' : y in eball x ε ↔ edist x y < ε := by rw [edist_comm, mem_eball]

/--
Definition of `closedEBall` / `closedEBall` 的定义

English:
definition closedEBall
  signature: (x : α) (ε : Real>=0∞)
  body: { y | edist y x <= ε }

中文:
定义 closedEBall
  签名: (x : α) (ε : 实数>=0∞)
  定义体: { y | edist y x <= ε }
-/
def closedEBall (x : α) (ε : Real>=0∞) :=
  { y | edist y x <= ε }

/--
theorem `mem_closedEBall` / 定理 `mem_closedEBall`

English:
theorem mem_closedEBall
  statement: y in closedEBall x ε ↔ edist y x <= ε
  proof: Iff.rfl

中文:
定理 mem_closedEBall
  结论: y in closedEBall x ε ↔ edist y x <= ε
  证明: Iff.rfl
-/
@[simp] theorem mem_closedEBall : y in closedEBall x ε ↔ edist y x <= ε := Iff.rfl

/--
theorem `mem_closedEBall'` / 定理 `mem_closedEBall'`

English:
theorem mem_closedEBall'
  statement: y in closedEBall x ε ↔ edist x y <= ε
  proof: by
  rw [edist_comm]; rw [mem_closedEBall]

@[simp]

中文:
定理 mem_closedEBall'
  结论: y in closedEBall x ε ↔ edist x y <= ε
  证明: by
  rw [edist_comm]; rw [mem_closedEBall]

@[simp]

Depends on / 依赖: edist_comm, mem_closedEBall
-/
theorem mem_closedEBall' : y in closedEBall x ε ↔ edist x y <= ε := by
  rw [edist_comm]; rw [mem_closedEBall]

@[simp]
/--
theorem `closedEBall_top` / 定理 `closedEBall_top`

English:
theorem closedEBall_top
  given: (x : α)
  statement: closedEBall x ∞ = univ
  proof: eq_univ_of_forall fun _ => mem_ofPred.2 le_top

中文:
定理 closedEBall_top
  条件: (x : α)
  结论: closedEBall x ∞ = univ
  证明: eq_univ_of_forall fun _ => mem_ofPred.2 le_top

Depends on / 依赖: eq_univ_of_forall, le_top, mem_ofPred
-/
theorem closedEBall_top (x : α) : closedEBall x ∞ = univ :=
  eq_univ_of_forall fun _ => mem_ofPred.2 le_top

/--
theorem `eball_subset_closedEBall` / 定理 `eball_subset_closedEBall`

English:
theorem eball_subset_closedEBall
  statement: eball x ε subseteq closedEBall x ε
  proof: fun _ h => le_of_lt h.out

中文:
定理 eball_subset_closedEBall
  结论: eball x ε subseteq closedEBall x ε
  证明: fun _ h => le_of_lt h.out

Depends on / 依赖: h.out, le_of_lt
-/
theorem eball_subset_closedEBall : eball x ε subseteq closedEBall x ε := fun _ h => le_of_lt h.out

/--
theorem `pos_of_mem_eball` / 定理 `pos_of_mem_eball`

English:
theorem pos_of_mem_eball
  given: (hy : y in eball x ε)
  statement: 0 < ε
  proof: hy.pos

中文:
定理 pos_of_mem_eball
  条件: (hy : y in eball x ε)
  结论: 0 < ε
  证明: hy.pos

Depends on / 依赖: hy.pos
-/
theorem pos_of_mem_eball (hy : y in eball x ε) : 0 < ε :=
  hy.pos

/--
theorem `mem_eball_self` / 定理 `mem_eball_self`

English:
theorem mem_eball_self
  given: (h : 0 < ε)
  statement: x in eball x ε
  proof: by
  rwa [mem_eball, edist_self]

中文:
定理 mem_eball_self
  条件: (h : 0 < ε)
  结论: x in eball x ε
  证明: by
  rwa [mem_eball, edist_self]

Depends on / 依赖: edist_self, mem_eball
-/
theorem mem_eball_self (h : 0 < ε) : x in eball x ε := by
  rwa [mem_eball, edist_self]

/--
theorem `mem_closedEBall_self` / 定理 `mem_closedEBall_self`

English:
theorem mem_closedEBall_self
  statement: x in closedEBall x ε
  proof: by
  rw [mem_closedEBall]; rw [edist_self]; apply zero_le

中文:
定理 mem_closedEBall_self
  结论: x in closedEBall x ε
  证明: by
  rw [mem_closedEBall]; rw [edist_self]; apply zero_le

Depends on / 依赖: edist_self, mem_closedEBall, zero_le
-/
theorem mem_closedEBall_self : x in closedEBall x ε := by
  rw [mem_closedEBall]; rw [edist_self]; apply zero_le

/--
theorem `mem_eball_comm` / 定理 `mem_eball_comm`

English:
theorem mem_eball_comm
  statement: x in eball y ε ↔ y in eball x ε
  proof: by rw [mem_eball', mem_eball]

中文:
定理 mem_eball_comm
  结论: x in eball y ε ↔ y in eball x ε
  证明: by rw [mem_eball', mem_eball]

Depends on / 依赖: mem_eball
-/
theorem mem_eball_comm : x in eball y ε ↔ y in eball x ε := by rw [mem_eball', mem_eball]

/--
theorem `mem_closedEBall_comm` / 定理 `mem_closedEBall_comm`

English:
theorem mem_closedEBall_comm
  statement: x in closedEBall y ε ↔ y in closedEBall x ε
  proof: by
  rw [mem_closedEBall']; rw [mem_closedEBall]

@[gcongr]

中文:
定理 mem_closedEBall_comm
  结论: x in closedEBall y ε ↔ y in closedEBall x ε
  证明: by
  rw [mem_closedEBall']; rw [mem_closedEBall]

@[gcongr]

Depends on / 依赖: mem_closedEBall
-/
theorem mem_closedEBall_comm : x in closedEBall y ε ↔ y in closedEBall x ε := by
  rw [mem_closedEBall']; rw [mem_closedEBall]

@[gcongr]
/--
theorem `eball_subset_eball` / 定理 `eball_subset_eball`

English:
theorem eball_subset_eball
  given: (h : ε₁ <= ε₂)
  statement: eball x ε₁ subseteq eball x ε₂
  proof: fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

@[gcongr]

中文:
定理 eball_subset_eball
  条件: (h : ε₁ <= ε₂)
  结论: eball x ε₁ subseteq eball x ε₂
  证明: fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

@[gcongr]
-/
theorem eball_subset_eball (h : ε₁ <= ε₂) : eball x ε₁ subseteq eball x ε₂ := fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

@[gcongr]
/--
theorem `closedEBall_subset_closedEBall` / 定理 `closedEBall_subset_closedEBall`

English:
theorem closedEBall_subset_closedEBall
  given: (h : ε₁ <= ε₂)
  statement: closedEBall x ε₁ subseteq closedEBall x ε₂
  proof: fun _y (yx : _ <= ε₁) => le_trans yx h

中文:
定理 closedEBall_subset_closedEBall
  条件: (h : ε₁ <= ε₂)
  结论: closedEBall x ε₁ subseteq closedEBall x ε₂
  证明: fun _y (yx : _ <= ε₁) => le_trans yx h

Depends on / 依赖: le_trans
-/
theorem closedEBall_subset_closedEBall (h : ε₁ <= ε₂) : closedEBall x ε₁ subseteq closedEBall x ε₂ :=
  fun _y (yx : _ <= ε₁) => le_trans yx h

/--
theorem `eball_disjoint` / 定理 `eball_disjoint`

English:
theorem eball_disjoint
  given: (h : ε₁ + ε₂ <= edist x y)
  statement: Disjoint (eball x ε₁) (eball y ε₂)
  proof: Set.disjoint_left.mpr fun z h₁ h₂ =>
(edist_triangle_left x y z).not_gt (ENNReal.add_lt_add h₁ h₂).trans_le h

中文:
定理 eball_disjoint
  条件: (h : ε₁ + ε₂ <= edist x y)
  结论: Disjoint (eball x ε₁) (eball y ε₂)
  证明: Set.disjoint_left.mpr fun z h₁ h₂ =>
(edist_triangle_left x y z).not_gt (ENNReal.add_lt_add h₁ h₂).trans_le h

Depends on / 依赖: ENNReal, ENNReal.add_lt_add, Set.disjoint_left.mpr, add_lt_add, disjoint_left, edist_triangle_left, not_gt, trans_le
-/
theorem eball_disjoint (h : ε₁ + ε₂ <= edist x y) : Disjoint (eball x ε₁) (eball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
(edist_triangle_left x y z).not_gt (ENNReal.add_lt_add h₁ h₂).trans_le h

/--
theorem `eball_subset` / 定理 `eball_subset`

English:
theorem eball_subset
  given: (h : edist x y + ε₁ <= ε₂) (h' : edist x y != ∞)
  statement: eball x ε₁ subseteq eball y ε₂
  proof: fun z zx =>
  calc
    edist z y <= edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_comm _ _
    _ < edist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ <= ε₂ := h

中文:
定理 eball_subset
  条件: (h : edist x y + ε₁ <= ε₂) (h' : edist x y != ∞)
  结论: eball x ε₁ subseteq eball y ε₂
  证明: fun z zx =>
  calc
    edist z y <= edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_comm _ _
    _ < edist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ <= ε₂ := h

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_left, add_comm, add_lt_add_left, edist_triangle
-/
theorem eball_subset (h : edist x y + ε₁ <= ε₂) (h' : edist x y != ∞) : eball x ε₁ subseteq eball y ε₂ :=
  fun z zx =>
  calc
    edist z y <= edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_comm _ _
    _ < edist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ <= ε₂ := h

/--
theorem `exists_eball_subset_eball` / 定理 `exists_eball_subset_eball`

English:
theorem exists_eball_subset_eball
  given: (h : y in eball x ε)
  statement: exists ε' > 0, eball y ε' subseteq eball x ε
  proof: by
  have : 0 < ε - edist y x := by simpa using h
  refine ⟨ε - edist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le

中文:
定理 存在_eball_subset_eball
  条件: (h : y in eball x ε)
  结论: 存在 ε' > 0, eball y ε' subseteq eball x ε
  证明: by
  have : 0 < ε - edist y x := by simpa using h
  refine ⟨ε - edist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le

Depends on / 依赖: add_tsub_cancel_of_le, eball_subset, mem_eball, mem_eball.mp, ne_top_of_lt
-/
theorem exists_eball_subset_eball (h : y in eball x ε) : exists ε' > 0, eball y ε' subseteq eball x ε := by
  have : 0 < ε - edist y x := by simpa using h
  refine ⟨ε - edist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le

/--
theorem `eball_eq_empty_iff` / 定理 `eball_eq_empty_iff`

English:
theorem eball_eq_empty_iff
  statement: eball x ε = ∅ ↔ ε = 0
  proof: eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩

中文:
定理 eball_eq_empty_iff
  结论: eball x ε = ∅ ↔ ε = 0
  证明: eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩

Depends on / 依赖: eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem.trans, le_bot_iff, le_of_eq, le_of_not_gt, mem_eball_self, not_lt_of_ge, pos_of_mem_eball
-/
theorem eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩

/--
theorem `ordConnected_setOfPred_closedEBall_subset` / 定理 `ordConnected_setOfPred_closedEBall_subset`

English:
theorem ordConnected_setOfPred_closedEBall_subset
  given: (x : α) (s : Set α)
  proof: ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_closedEBall_subset := ordConnected_setOfPred_closedEBall_subset

中文:
定理 ordConnected_setOfPred_closedEBall_subset
  条件: (x : α) (s : 集合 α)
  证明: ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_closedEBall_subset := ordConnected_setOfPred_closedEBall_subset

Depends on / 依赖: closedEBall_subset_closedEBall
-/
theorem ordConnected_setOfPred_closedEBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedEBall x r subseteq s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_closedEBall_subset := ordConnected_setOfPred_closedEBall_subset

/--
theorem `ordConnected_setOfPred_eball_subset` / 定理 `ordConnected_setOfPred_eball_subset`

English:
theorem ordConnected_setOfPred_eball_subset
  given: (x : α) (s : Set α)
  proof: ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_eball_subset := ordConnected_setOfPred_eball_subset

中文:
定理 ordConnected_setOfPred_eball_subset
  条件: (x : α) (s : 集合 α)
  证明: ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_eball_subset := ordConnected_setOfPred_eball_subset

Depends on / 依赖: eball_subset_eball
-/
theorem ordConnected_setOfPred_eball_subset (x : α) (s : Set α) :
    OrdConnected { r | eball x r subseteq s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_eball_subset := ordConnected_setOfPred_eball_subset

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
@[instance_reducible]
/--
Definition of `edistLtTopSetoid` / `edistLtTopSetoid` 的定义

English:
definition edistLtTopSetoid
  signature: : Setoid α where
  body: edist x y < ⊤
  iseqv :=
    { refl x := by rw [edist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [edist_comm]
      trans hxy hyz := lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

@[simp]

中文:
定义 edistLtTopSetoid
  签名: : 集合等价关系 α where
  定义体: edist x y < ⊤
  iseqv :=
    { refl x := by rw [edist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [edist_comm]
      trans hxy hyz := lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

@[simp]
-/
def edistLtTopSetoid : Setoid α where
  r x y := edist x y < ⊤
  iseqv :=
    { refl x := by rw [edist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [edist_comm]
      trans hxy hyz := lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

@[simp]
/--
theorem `eball_zero` / 定理 `eball_zero`

English:
theorem eball_zero
  statement: eball x 0 = ∅
  proof: by rw [eball_eq_empty_iff]

中文:
定理 eball_zero
  结论: eball x 0 = ∅
  证明: by rw [eball_eq_empty_iff]

Depends on / 依赖: eball_eq_empty_iff
-/
theorem eball_zero : eball x 0 = ∅ := by rw [eball_eq_empty_iff]

/--
theorem `nhds_basis_eball` / 定理 `nhds_basis_eball`

English:
theorem nhds_basis_eball
  statement: (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (eball x)
  proof: nhds_basis_uniformity uniformity_basis_edist

中文:
定理 nhds_basis_eball
  结论: (𝓝 x).有基 (fun ε : 实数>=0∞ => 0 < ε) (eball x)
  证明: nhds_basis_uniformity uniformity_basis_edist

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_edist
-/
theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (eball x) :=
  nhds_basis_uniformity uniformity_basis_edist

/--
theorem `nhdsWithin_basis_eball` / 定理 `nhdsWithin_basis_eball`

English:
theorem nhdsWithin_basis_eball
  statement: (𝓝[s] x).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε => eball x ε inter s
  proof: nhdsWithin_hasBasis nhds_basis_eball s

中文:
定理 nhdsWithin_basis_eball
  结论: (𝓝[s] x).有基 (fun ε : 实数>=0∞ => 0 < ε) fun ε => eball x ε inter s
  证明: nhdsWithin_hasBasis nhds_basis_eball s

Depends on / 依赖: nhdsWithin_hasBasis, nhds_basis_eball
-/
theorem nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε => eball x ε inter s :=
  nhdsWithin_hasBasis nhds_basis_eball s

/--
theorem `nhds_basis_closedEBall` / 定理 `nhds_basis_closedEBall`

English:
theorem nhds_basis_closedEBall
  statement: (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (closedEBall x)
  proof: nhds_basis_uniformity uniformity_basis_edist_le

中文:
定理 nhds_basis_closedEBall
  结论: (𝓝 x).有基 (fun ε : 实数>=0∞ => 0 < ε) (closedEBall x)
  证明: nhds_basis_uniformity uniformity_basis_edist_le

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_edist_le
-/
theorem nhds_basis_closedEBall : (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (closedEBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le

/--
theorem `nhdsWithin_basis_closedEBall` / 定理 `nhdsWithin_basis_closedEBall`

English:
theorem nhdsWithin_basis_closedEBall
  proof: nhdsWithin_hasBasis nhds_basis_closedEBall s

中文:
定理 nhdsWithin_basis_closedEBall
  证明: nhdsWithin_hasBasis nhds_basis_closedEBall s

Depends on / 依赖: nhdsWithin_hasBasis, nhds_basis_closedEBall
-/
theorem nhdsWithin_basis_closedEBall :
    (𝓝[s] x).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε => closedEBall x ε inter s :=
  nhdsWithin_hasBasis nhds_basis_closedEBall s

end Metric

namespace EMetric
variable {x : α} {ε : Real>=0∞} {s t : Set α}

open Metric

/--
theorem `nhds_eq` / 定理 `nhds_eq`

English:
theorem nhds_eq
  statement: 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε)
  proof: nhds_basis_eball.eq_biInf

中文:
定理 nhds_eq
  结论: 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε)
  证明: nhds_basis_eball.eq_biInf

Depends on / 依赖: eq_biInf, nhds_basis_eball, nhds_basis_eball.eq_biInf
-/
theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε) :=
  nhds_basis_eball.eq_biInf

/--
theorem `mem_nhds_iff` / 定理 `mem_nhds_iff`

English:
theorem mem_nhds_iff
  statement: s in 𝓝 x ↔ exists ε > 0, eball x ε subseteq s
  proof: nhds_basis_eball.mem_iff

中文:
定理 mem_nhds_iff
  结论: s in 𝓝 x ↔ 存在 ε > 0, eball x ε subseteq s
  证明: nhds_basis_eball.mem_iff

Depends on / 依赖: mem_iff, nhds_basis_eball, nhds_basis_eball.mem_iff
-/
theorem mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, eball x ε subseteq s :=
  nhds_basis_eball.mem_iff

/--
theorem `mem_nhdsWithin_iff` / 定理 `mem_nhdsWithin_iff`

English:
theorem mem_nhdsWithin_iff
  statement: s in 𝓝[t] x ↔ exists ε > 0, eball x ε inter t subseteq s
  proof: nhdsWithin_basis_eball.mem_iff

中文:
定理 mem_nhdsWithin_iff
  结论: s in 𝓝[t] x ↔ 存在 ε > 0, eball x ε inter t subseteq s
  证明: nhdsWithin_basis_eball.mem_iff

Depends on / 依赖: mem_iff, nhdsWithin_basis_eball, nhdsWithin_basis_eball.mem_iff
-/
theorem mem_nhdsWithin_iff : s in 𝓝[t] x ↔ exists ε > 0, eball x ε inter t subseteq s :=
  nhdsWithin_basis_eball.mem_iff

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  statement: IsOpen s ↔ forall x in s, exists ε > 0, eball x ε subseteq s
  proof: by
  simp [isOpen_iff_nhds, mem_nhds_iff]

中文:
定理 isOpen_iff
  结论: 是开集 s ↔ 对任意 x in s, 存在 ε > 0, eball x ε subseteq s
  证明: by
  simp [isOpen_iff_nhds, mem_nhds_iff]

Depends on / 依赖: isOpen_iff_nhds, mem_nhds_iff
-/
theorem isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, eball x ε subseteq s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  statement: x in closure s ↔ forall ε > 0, exists y in s, edist x y < ε
  proof: (mem_closure_iff_nhds_basis nhds_basis_eball).trans by simp only [mem_eball, edist_comm x]

中文:
定理 mem_closure_iff
  结论: x in closure s ↔ 对任意 ε > 0, 存在 y in s, edist x y < ε
  证明: (mem_closure_iff_nhds_basis nhds_basis_eball).trans by simp only [mem_eball, edist_comm x]

Depends on / 依赖: edist_comm, mem_closure_iff_nhds_basis, mem_eball, nhds_basis_eball
-/
theorem mem_closure_iff : x in closure s ↔ forall ε > 0, exists y in s, edist x y < ε :=
(mem_closure_iff_nhds_basis nhds_basis_eball).trans by simp only [mem_eball, edist_comm x]

/--
lemma `dense_iff` / 引理 `dense_iff`

English:
lemma dense_iff
  statement: Dense s ↔ forall (x : α), forall r > 0, (eball x r inter s).Nonempty
  proof: forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']

中文:
引理 dense_iff
  结论: 稠密 s ↔ 对任意 (x : α), 对任意 r > 0, (eball x r inter s).非空
  证明: forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']

Depends on / 依赖: Nonempty, Set.Nonempty, and_comm, forall_congr, mem_closure_iff, mem_eball, mem_inter_iff
-/
lemma dense_iff : Dense s ↔ forall (x : α), forall r > 0, (eball x r inter s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  given: {f : Filter β} {u : β -> α} {a : α}
  proof: nhds_basis_eball.tendsto_right_iff

中文:
定理 tendsto_nhds
  条件: {f : 滤子 β} {u : β -> α} {a : α}
  证明: nhds_basis_eball.tendsto_right_iff

Depends on / 依赖: nhds_basis_eball, nhds_basis_eball.tendsto_right_iff, tendsto_right_iff
-/
theorem tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
    Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α}
  proof: (atTop_basis.tendsto_iff nhds_basis_eball).trans by
    simp only [true_and, mem_Ici, mem_eball]

中文:
定理 tendsto_atTop
  条件: [非空 β] [SemilatticeSup β] {u : β -> α} {a : α}
  证明: (atTop_basis.tendsto_iff nhds_basis_eball).trans by
    simp only [true_and, mem_Ici, mem_eball]

Depends on / 依赖: atTop_basis, atTop_basis.tendsto_iff, mem_Ici, mem_eball, nhds_basis_eball, tendsto_iff, true_and
-/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N, edist (u n) a < ε :=
(atTop_basis.tendsto_iff nhds_basis_eball).trans by
    simp only [true_and, mem_Ici, mem_eball]

section

variable [PseudoEMetricSpace β] {f : α -> β}

/--
theorem `tendsto_nhdsWithin_nhdsWithin` / 定理 `tendsto_nhdsWithin_nhdsWithin`

English:
theorem tendsto_nhdsWithin_nhdsWithin
  given: {t : Set β} {a b}
  proof: (nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto

中文:
定理 tendsto_nhdsWithin_nhdsWithin
  条件: {t : 集合 β} {a b}
  证明: (nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto

Depends on / 依赖: and_congr_right, exists_congr, forall_congr, nhdsWithin_basis_eball, nhdsWithin_basis_eball.tendsto_iff, tendsto_iff
-/
theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      forall ε > 0, exists δ > 0, forall ⦃x⦄, x in s -> edist x a < δ -> f x in t ∧ edist (f x) b < ε :=
(nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto

/--
theorem `tendsto_nhdsWithin_nhds` / 定理 `tendsto_nhdsWithin_nhds`

English:
theorem tendsto_nhdsWithin_nhds
  given: {a b}
  proof: by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

中文:
定理 tendsto_nhdsWithin_nhds
  条件: {a b}
  证明: by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

Depends on / 依赖: mem_univ, nhdsWithin_univ, tendsto_nhdsWithin_nhdsWithin, true_and
-/
theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      forall ε > 0, exists δ > 0, forall {x : α}, x in s -> edist x a < δ -> edist (f x) b < ε := by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

/--
theorem `tendsto_nhds_nhds` / 定理 `tendsto_nhds_nhds`

English:
theorem tendsto_nhds_nhds
  given: {a b}
  proof: nhds_basis_eball.tendsto_iff nhds_basis_eball

中文:
定理 tendsto_nhds_nhds
  条件: {a b}
  证明: nhds_basis_eball.tendsto_iff nhds_basis_eball

Depends on / 依赖: nhds_basis_eball, nhds_basis_eball.tendsto_iff, tendsto_iff
-/
theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x⦄, edist x a < δ -> edist (f x) b < ε :=
  nhds_basis_eball.tendsto_iff nhds_basis_eball

/--
theorem `continuousAt_iff` / 定理 `continuousAt_iff`

English:
theorem continuousAt_iff
  given: {a}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

中文:
定理 continuousAt_iff
  条件: {a}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

Depends on / 依赖: ContinuousAt, tendsto_nhds_nhds
-/
theorem continuousAt_iff {a} :
    ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, edist x a < δ -> edist (f x) (f a) < ε := by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

/--
theorem `continuousWithinAt_iff` / 定理 `continuousWithinAt_iff`

English:
theorem continuousWithinAt_iff
  given: {a s}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

中文:
定理 continuousWithinAt_iff
  条件: {a s}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

Depends on / 依赖: ContinuousWithinAt, tendsto_nhdsWithin_nhds
-/
theorem continuousWithinAt_iff {a s} :
    ContinuousWithinAt f s a ↔
      forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x in s -> edist x a < δ -> edist (f x) (f a) < ε := by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

/--
theorem `continuousOn_iff` / 定理 `continuousOn_iff`

English:
theorem continuousOn_iff
  given: {s}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff]

中文:
定理 continuousOn_iff
  条件: {s}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff]

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff
-/
theorem continuousOn_iff {s} :
    ContinuousOn f s ↔
      forall b in s, forall ε > 0, exists δ > 0, forall a in s, edist a b < δ -> edist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]

/--
theorem `continuous_iff` / 定理 `continuous_iff`

English:
theorem continuous_iff
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

中文:
定理 continuous_iff
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds_nhds
-/
theorem continuous_iff :
    Continuous f ↔ forall b, forall ε > 0, exists δ > 0, forall a, edist a b < δ -> edist (f a) (f b) < ε :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

end

section

variable [TopologicalSpace β] {f : β -> α}

/--
theorem `continuousAt_iff'` / 定理 `continuousAt_iff'`

English:
theorem continuousAt_iff'
  given: {b}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds]

中文:
定理 continuousAt_iff'
  条件: {b}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds]

Depends on / 依赖: ContinuousAt, tendsto_nhds
-/
theorem continuousAt_iff' {b} :
    ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, edist (f x) (f b) < ε := by
  rw [ContinuousAt]; rw [tendsto_nhds]

/--
theorem `continuousWithinAt_iff'` / 定理 `continuousWithinAt_iff'`

English:
theorem continuousWithinAt_iff'
  given: {b s}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

中文:
定理 continuousWithinAt_iff'
  条件: {b s}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

Depends on / 依赖: ContinuousWithinAt, tendsto_nhds
-/
theorem continuousWithinAt_iff' {b s} :
    ContinuousWithinAt f s b ↔ forall ε > 0, forallᶠ x in 𝓝[s] b, edist (f x) (f b) < ε := by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

/--
theorem `continuousOn_iff'` / 定理 `continuousOn_iff'`

English:
theorem continuousOn_iff'
  given: {s}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff']

中文:
定理 continuousOn_iff'
  条件: {s}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff']

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff
-/
theorem continuousOn_iff' {s} :
    ContinuousOn f s ↔ forall b in s, forall ε > 0, forallᶠ x in 𝓝[s] b, edist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']

/--
theorem `continuous_iff'` / 定理 `continuous_iff'`

English:
theorem continuous_iff'
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

中文:
定理 continuous_iff'
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds
-/
theorem continuous_iff' :
    Continuous f ↔ forall a, forall ε > 0, forallᶠ x in 𝓝 a, edist (f x) (f a) < ε :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

end

end EMetric

namespace Metric
variable {x : α} {ε : Real>=0∞} {s t : Set α}

/--
theorem `isOpen_eball` / 定理 `isOpen_eball`

English:
theorem isOpen_eball
  statement: IsOpen (eball x ε)
  proof: EMetric.isOpen_iff.2 fun _ => exists_eball_subset_eball

中文:
定理 isOpen_eball
  结论: 是开集 (eball x ε)
  证明: EMetric.isOpen_iff.2 fun _ => exists_eball_subset_eball
-/
@[simp] theorem isOpen_eball : IsOpen (eball x ε) :=
  EMetric.isOpen_iff.2 fun _ => exists_eball_subset_eball

/--
theorem `isClosed_eball_top` / 定理 `isClosed_eball_top`

English:
theorem isClosed_eball_top
  statement: IsClosed (eball x ⊤)
  proof: isOpen_compl_iff.1 EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩

中文:
定理 isClosed_eball_top
  结论: 是闭集 (eball x ⊤)
  证明: isOpen_compl_iff.1 EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩

Depends on / 依赖: EMetric, EMetric.isOpen_iff, ENNReal, ENNReal.coe_lt_top, coe_lt_top, edistLtTopSetoid, edistLtTopSetoid.symm, edistLtTopSetoid.trans, isOpen_compl_iff, isOpen_iff
-/
theorem isClosed_eball_top : IsClosed (eball x ⊤) :=
isOpen_compl_iff.1 EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩

/--
theorem `eball_mem_nhds` / 定理 `eball_mem_nhds`

English:
theorem eball_mem_nhds
  given: (x : α) {ε : Real>=0∞} (ε0 : 0 < ε)
  statement: eball x ε in 𝓝 x
  proof: isOpen_eball.mem_nhds (mem_eball_self ε0)

中文:
定理 eball_mem_nhds
  条件: (x : α) {ε : 实数>=0∞} (ε0 : 0 < ε)
  结论: eball x ε in 𝓝 x
  证明: isOpen_eball.mem_nhds (mem_eball_self ε0)

Depends on / 依赖: isOpen_eball, isOpen_eball.mem_nhds, mem_eball_self, mem_nhds
-/
theorem eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε) : eball x ε in 𝓝 x :=
  isOpen_eball.mem_nhds (mem_eball_self ε0)

/--
theorem `closedEBall_mem_nhds` / 定理 `closedEBall_mem_nhds`

English:
theorem closedEBall_mem_nhds
  given: (x : α) {ε : Real>=0∞} (ε0 : 0 < ε)
  statement: closedEBall x ε in 𝓝 x
  proof: mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall

中文:
定理 closedEBall_mem_nhds
  条件: (x : α) {ε : 实数>=0∞} (ε0 : 0 < ε)
  结论: closedEBall x ε in 𝓝 x
  证明: mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall

Depends on / 依赖: eball_mem_nhds, eball_subset_closedEBall, mem_of_superset
-/
theorem closedEBall_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε) : closedEBall x ε in 𝓝 x :=
  mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall

/--
theorem `eball_prod_same` / 定理 `eball_prod_same`

English:
theorem eball_prod_same
  given: [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞)
  proof: ext fun z => by simp [Prod.edist_eq]

中文:
定理 eball_prod_same
  条件: [PseudoEMetric空间 β] (x : α) (y : β) (r : 实数>=0∞)
  证明: ext fun z => by simp [Prod.edist_eq]

Depends on / 依赖: Prod.edist_eq, edist_eq
-/
theorem eball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞) :
    eball x r ×ˢ eball y r = eball (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]

/--
theorem `closedEBall_prod_same` / 定理 `closedEBall_prod_same`

English:
theorem closedEBall_prod_same
  given: [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞)
  proof: ext fun z => by simp [Prod.edist_eq]

中文:
定理 closedEBall_prod_same
  条件: [PseudoEMetric空间 β] (x : α) (y : β) (r : 实数>=0∞)
  证明: ext fun z => by simp [Prod.edist_eq]

Depends on / 依赖: Prod.edist_eq, edist_eq
-/
theorem closedEBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞) :
    closedEBall x r ×ˢ closedEBall y r = closedEBall (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-24")] alias ball := eball
@[deprecated (since := "2026-01-24")] alias mem_ball := mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball' := mem_eball'
@[deprecated (since := "2026-01-24")] alias closedBall := closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall := mem_closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall' := mem_closedEBall'
@[deprecated (since := "2026-01-24")] alias closedBall_top := closedEBall_top
@[deprecated (since := "2026-01-24")] alias ball_subset_closedBall := eball_subset_closedEBall
@[deprecated (since := "2026-01-24")] alias pos_of_mem_ball := pos_of_mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball_self := mem_eball_self
@[deprecated (since := "2026-01-24")] alias mem_closedBall_self := mem_closedEBall_self
@[deprecated (since := "2026-01-24")] alias mem_ball_comm := mem_eball_comm
@[deprecated (since := "2026-01-24")] alias mem_closedBall_comm := mem_closedEBall_comm
@[deprecated (since := "2026-01-24")] alias ball_subset_ball := eball_subset_eball

@[deprecated (since := "2026-01-24")]
alias closedBall_subset_closedBall := closedEBall_subset_closedEBall

@[deprecated (since := "2026-01-24")] alias ball_disjoint := eball_disjoint
@[deprecated (since := "2026-01-24")] alias ball_subset := eball_subset
@[deprecated (since := "2026-01-24")] alias exists_ball_subset_ball := exists_eball_subset_eball
@[deprecated (since := "2026-01-24")] alias ball_eq_empty_iff := eball_eq_empty_iff

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_closedBall_subset := ordConnected_setOfPred_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_ball_subset := ordConnected_setOfPred_eball_subset

@[deprecated (since := "2026-01-24")] alias edistLtTopSetoid := edistLtTopSetoid
@[deprecated (since := "2026-01-24")] alias ball_zero := eball_zero

@[deprecated (since := "2026-01-24")]
protected alias nhds_basis_eball := nhds_basis_eball

@[deprecated (since := "2026-01-24")] alias nhdsWithin_basis_eball := nhdsWithin_basis_eball
@[deprecated (since := "2026-01-24")] alias nhds_basis_closed_eball := nhds_basis_closedEBall

@[deprecated (since := "2026-01-24")]
alias nhdsWithin_basis_closed_eball := nhdsWithin_basis_closedEBall

@[deprecated (since := "2026-01-24")] alias isOpen_ball := isOpen_eball
@[deprecated (since := "2026-01-24")] alias isClosed_ball_top := isClosed_eball_top
@[deprecated (since := "2026-01-24")] alias ball_mem_nhds := eball_mem_nhds
@[deprecated (since := "2026-01-24")] alias closedBall_mem_nhds := closedEBall_mem_nhds
@[deprecated (since := "2026-01-24")] alias ball_prod_same := eball_prod_same
@[deprecated (since := "2026-01-24")] alias closedBall_prod_same := closedEBall_prod_same

end EMetric

namespace Subtype

open Metric

@[simp]
/--
theorem `preimage_eball` / 定理 `preimage_eball`

English:
theorem preimage_eball
  given: {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞)
  proof: rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricBall := preimage_eball

@[simp]

中文:
定理 preimage_eball
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数>=0∞)
  证明: rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricBall := preimage_eball

@[simp]
-/
theorem preimage_eball {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) :
    Subtype.val ⁻¹' (eball a.1 r) = eball a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricBall := preimage_eball

@[simp]
/--
theorem `preimage_closedEBall` / 定理 `preimage_closedEBall`

English:
theorem preimage_closedEBall
  given: {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞)
  proof: rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricClosedBall := preimage_closedEBall

@[simp]

中文:
定理 preimage_closedEBall
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数>=0∞)
  证明: rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricClosedBall := preimage_closedEBall

@[simp]
-/
theorem preimage_closedEBall {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) :
    Subtype.val ⁻¹' (closedEBall a.1 r) = closedEBall a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricClosedBall := preimage_closedEBall

@[simp]
/--
theorem `image_eball` / 定理 `image_eball`

English:
theorem image_eball
  given: {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞)
  proof: by
  rw [← preimage_eball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricBall := image_eball

@[simp]

中文:
定理 image_eball
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数>=0∞)
  证明: by
  rw [← preimage_eball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricBall := image_eball

@[simp]

Depends on / 依赖: image_preimage_eq_inter_range, preimage_eball, range_val_subtype
-/
theorem image_eball {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) :
    Subtype.val '' (eball a r) = eball a.1 r inter {a | p a} := by
  rw [← preimage_eball]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricBall := image_eball

@[simp]
/--
theorem `image_closedEBall` / 定理 `image_closedEBall`

English:
theorem image_closedEBall
  given: {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞)
  proof: by
  rw [← preimage_closedEBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricClosedBall := image_closedEBall

中文:
定理 image_closedEBall
  条件: {p : α -> 命题} (a : {a // p a}) (r : 实数>=0∞)
  证明: by
  rw [← preimage_closedEBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricClosedBall := image_closedEBall

Depends on / 依赖: image_preimage_eq_inter_range, preimage_closedEBall, range_val_subtype
-/
theorem image_closedEBall {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) :
    Subtype.val '' (closedEBall a r) = closedEBall a.1 r inter {a | p a} := by
  rw [← preimage_closedEBall]; rw [image_preimage_eq_inter_range]; rw [range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricClosedBall := image_closedEBall

end Subtype

/--
Definition of `EMetricSpace` / `EMetricSpace` 的定义

English:
class EMetricSpace
  parameters: (α : Type u)
  extends: PseudoEMetricSpace α
  axioms and operations (1):
    - eq_of_edist_eq_zero : forall {x y : α}, edist x y = 0 -> x = y

中文:
类 广义度量空间
  参数: (α : 类型u)
  继承: PseudoEMetric空间 α
  公理与运算 (1 个):
    - eq_of_edist_eq_zero : 对任意 {x y : α}, edist x y = 0 -> x = y
-/
class EMetricSpace (α : Type u) : Type u extends PseudoEMetricSpace α where
  eq_of_edist_eq_zero : forall {x y : α}, edist x y = 0 -> x = y

@[ext]
/--
theorem `EMetricSpace.ext` / 定理 `EMetricSpace.ext`

English:
theorem EMetricSpace.ext
  proof: by
  cases m
  cases m'
  congr
  ext1
  assumption

中文:
定理 广义度量空间.ext
  证明: by
  cases m
  cases m'
  congr
  ext1
  assumption
-/
protected theorem EMetricSpace.ext
    {α : Type*} {m m' : EMetricSpace α} (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

variable {γ : Type w} [EMetricSpace γ]

export EMetricSpace (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
/--
theorem `edist_eq_zero` / 定理 `edist_eq_zero`

English:
theorem edist_eq_zero
  given: {x y : γ}
  statement: edist x y = 0 ↔ x = y
  proof: ⟨eq_of_edist_eq_zero, fun h => h ▸ edist_self _⟩

@[simp]

中文:
定理 edist_eq_zero
  条件: {x y : γ}
  结论: edist x y = 0 ↔ x = y
  证明: ⟨eq_of_edist_eq_zero, fun h => h ▸ edist_self _⟩

@[simp]

Depends on / 依赖: edist_self, eq_of_edist_eq_zero
-/
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  ⟨eq_of_edist_eq_zero, fun h => h ▸ edist_self _⟩

@[simp]
/--
theorem `zero_eq_edist` / 定理 `zero_eq_edist`

English:
theorem zero_eq_edist
  given: {x y : γ}
  statement: 0 = edist x y ↔ x = y
  proof: eq_comm.trans edist_eq_zero

中文:
定理 zero_eq_edist
  条件: {x y : γ}
  结论: 0 = edist x y ↔ x = y
  证明: eq_comm.trans edist_eq_zero

Depends on / 依赖: edist_eq_zero, eq_comm, eq_comm.trans
-/
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y := eq_comm.trans edist_eq_zero

/--
theorem `edist_le_zero` / 定理 `edist_le_zero`

English:
theorem edist_le_zero
  given: {x y : γ}
  statement: edist x y <= 0 ↔ x = y
  proof: nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]

中文:
定理 edist_le_zero
  条件: {x y : γ}
  结论: edist x y <= 0 ↔ x = y
  证明: nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]

Depends on / 依赖: edist_eq_zero, nonpos_iff_eq_zero, nonpos_iff_eq_zero.trans
-/
theorem edist_le_zero {x y : γ} : edist x y <= 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]
/--
theorem `edist_pos` / 定理 `edist_pos`

English:
theorem edist_pos
  given: {x y : γ}
  statement: 0 < edist x y ↔ x != y
  proof: by simp [← not_le]

中文:
定理 edist_pos
  条件: {x y : γ}
  结论: 0 < edist x y ↔ x != y
  证明: by simp [← not_le]

Depends on / 依赖: not_le
-/
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x != y := by simp [← not_le]

/--
lemma `Metric.closedEBall_zero` / 引理 `Metric.closedEBall_zero`

English:
lemma Metric.closedEBall_zero
  given: (x : γ)
  statement: closedEBall x 0 = {x}
  proof: by ext; simp

@[deprecated (since := "2026-01-24")]
alias EMetric.closedBall_zero := Metric.closedEBall_zero

中文:
引理 Metric.closedEBall_zero
  条件: (x : γ)
  结论: closedEBall x 0 = {x}
  证明: by ext; simp

@[deprecated (since := "2026-01-24")]
alias EMetric.closedBall_zero := Metric.closedEBall_zero
-/
@[simp] lemma Metric.closedEBall_zero (x : γ) : closedEBall x 0 = {x} := by ext; simp

@[deprecated (since := "2026-01-24")]
alias EMetric.closedBall_zero := Metric.closedEBall_zero

/--
theorem `eq_of_forall_edist_le` / 定理 `eq_of_forall_edist_le`

English:
theorem eq_of_forall_edist_le
  given: {x y : γ} (h : forall ε > 0, edist x y <= ε)
  statement: x = y
  proof: eq_of_edist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

中文:
定理 eq_of_对任意_edist_le
  条件: {x y : γ} (h : 对任意 ε > 0, edist x y <= ε)
  结论: x = y
  证明: eq_of_edist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

Depends on / 依赖: bot_le, eq_of_edist_eq_zero, eq_of_le_of_forall_lt_imp_le_of_dense
-/
theorem eq_of_forall_edist_le {x y : γ} (h : forall ε > 0, edist x y <= ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

/--
Definition of `EMetricSpace.replaceUniformity` / `EMetricSpace.replaceUniformity` 的定义

English:
abbreviation EMetricSpace.replaceUniformity
  signature: {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
  body: @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)

中文:
缩写 广义度量空间.replaceUniformity
  签名: {γ} [U : 一致空间 γ] (m : 广义度量空间 γ)
  定义体: @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)

Depends on / 依赖: m.toEDist, toEDist
-/
abbrev EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)

/--
Definition of `EMetricSpace.replaceTopology` / `EMetricSpace.replaceTopology` 的定义

English:
abbreviation EMetricSpace.replaceTopology
  signature: {γ} [T : TopologicalSpace γ] (m : EMetricSpace γ)
  body: @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_edist := PseudoEMetricSpace.uniformity_edist

中文:
缩写 广义度量空间.replaceTopology
  签名: {γ} [T : 拓扑空间 γ] (m : 广义度量空间 γ)
  定义体: @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_edist := PseudoEMetricSpace.uniformity_edist

Depends on / 依赖: m.toEDist, toEDist
-/
abbrev EMetricSpace.replaceTopology {γ} [T : TopologicalSpace γ] (m : EMetricSpace γ)
    (H : T = m.toUniformSpace.toTopologicalSpace) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_edist := PseudoEMetricSpace.uniformity_edist

/--
Definition of `EMetricSpace.induced` / `EMetricSpace.induced` 的定义

English:
abbreviation EMetricSpace.induced
  signature: {γ β} (f : γ -> β) (hf : Function.Injective f) (m : EMetricSpace β)
  body: { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }

中文:
缩写 广义度量空间.induced
  签名: {γ β} (f : γ -> β) (hf : 函数.单射 f) (m : 广义度量空间 β)
  定义体: { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.induced, edist_eq_zero, eq_of_edist_eq_zero, induced, m.toPseudoEMetricSpace, toPseudoEMetricSpace
-/
abbrev EMetricSpace.induced {γ β} (f : γ -> β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ :=
  { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }

/-- EMetric space instance on subsets of emetric spaces -/
instance {α : Type*} {p : α -> Prop} [EMetricSpace α] : EMetricSpace (Subtype p) :=
  EMetricSpace.induced Subtype.val Subtype.coe_injective ‹_›

/-- EMetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive /-- EMetric space instance on the additive opposite of an emetric space. -/]
instance {α : Type*} [EMetricSpace α] : EMetricSpace αᵐᵒᵖ :=
  EMetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance {α : Type*} [EMetricSpace α] : EMetricSpace (ULift α) :=
  EMetricSpace.induced ULift.down ULift.down_injective ‹_›

/--
theorem `uniformity_edist` / 定理 `uniformity_edist`

English:
theorem uniformity_edist
  statement: 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε }
  proof: PseudoEMetricSpace.uniformity_edist

中文:
定理 uniformity_edist
  结论: 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε }
  证明: PseudoEMetricSpace.uniformity_edist

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.uniformity_edist, uniformity_edist
-/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [EDist X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist (Additive X)
  body: ‹EDist X›

中文:
实例 :
  签名: EDist (加性 X)
  定义体: ‹EDist X›
-/
instance : EDist (Additive X) := ‹EDist X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist (Multiplicative X)
  body: ‹EDist X›

@[simp]

中文:
实例 :
  签名: EDist (Multiplicative X)
  定义体: ‹EDist X›

@[simp]
-/
instance : EDist (Multiplicative X) := ‹EDist X›

@[simp]
/--
theorem `edist_ofMul` / 定理 `edist_ofMul`

English:
theorem edist_ofMul
  given: (a b : X)
  statement: edist (ofMul a) (ofMul b) = edist a b
  proof: rfl

@[simp]

中文:
定理 edist_ofMul
  条件: (a b : X)
  结论: edist (ofMul a) (ofMul b) = edist a b
  证明: rfl

@[simp]
-/
theorem edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b :=
  rfl

@[simp]
/--
theorem `edist_ofAdd` / 定理 `edist_ofAdd`

English:
theorem edist_ofAdd
  given: (a b : X)
  statement: edist (ofAdd a) (ofAdd b) = edist a b
  proof: rfl

@[simp]

中文:
定理 edist_ofAdd
  条件: (a b : X)
  结论: edist (ofAdd a) (ofAdd b) = edist a b
  证明: rfl

@[simp]
-/
theorem edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b :=
  rfl

@[simp]
/--
theorem `edist_toMul` / 定理 `edist_toMul`

English:
theorem edist_toMul
  given: (a b : Additive X)
  statement: edist a.toMul b.toMul = edist a b
  proof: rfl

@[simp]

中文:
定理 edist_toMul
  条件: (a b : 加性 X)
  结论: edist a.toMul b.toMul = edist a b
  证明: rfl

@[simp]
-/
theorem edist_toMul (a b : Additive X) : edist a.toMul b.toMul = edist a b :=
  rfl

@[simp]
/--
theorem `edist_toAdd` / 定理 `edist_toAdd`

English:
theorem edist_toAdd
  given: (a b : Multiplicative X)
  statement: edist a.toAdd b.toAdd = edist a b
  proof: rfl

中文:
定理 edist_toAdd
  条件: (a b : Multiplicative X)
  结论: edist a.toAdd b.toAdd = edist a b
  证明: rfl
-/
theorem edist_toAdd (a b : Multiplicative X) : edist a.toAdd b.toAdd = edist a b :=
  rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : PseudoEMetricSpace (Additive X)
  body: ‹PseudoEMetricSpace X›

中文:
实例 [PseudoEMetric空间
  签名: X] : PseudoEMetric空间 (加性 X)
  定义体: ‹PseudoEMetricSpace X›
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Additive X) := ‹PseudoEMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : PseudoEMetricSpace (Multiplicative X)
  body: ‹PseudoEMetricSpace X›

中文:
实例 [PseudoEMetric空间
  签名: X] : PseudoEMetric空间 (Multiplicative X)
  定义体: ‹PseudoEMetricSpace X›

Depends on / 依赖: PseudoEMetricSpace
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Multiplicative X) := ‹PseudoEMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EMetricSpace
  signature: X] : EMetricSpace (Additive X)
  body: ‹EMetricSpace X›

中文:
实例 [广义度量空间
  签名: X] : 广义度量空间 (加性 X)
  定义体: ‹EMetricSpace X›

Depends on / 依赖: EMetricSpace
-/
instance [EMetricSpace X] : EMetricSpace (Additive X) := ‹EMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EMetricSpace
  signature: X] : EMetricSpace (Multiplicative X)
  body: ‹EMetricSpace X›

中文:
实例 [广义度量空间
  签名: X] : 广义度量空间 (Multiplicative X)
  定义体: ‹EMetricSpace X›

Depends on / 依赖: EMetricSpace
-/
instance [EMetricSpace X] : EMetricSpace (Multiplicative X) := ‹EMetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [EDist X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist Xᵒᵈ
  body: ‹EDist X›

@[simp]

中文:
实例 :
  签名: EDist Xᵒᵈ
  定义体: ‹EDist X›

@[simp]
-/
instance : EDist Xᵒᵈ := ‹EDist X›

@[simp]
/--
theorem `edist_toDual` / 定理 `edist_toDual`

English:
theorem edist_toDual
  given: (a b : X)
  statement: edist (toDual a) (toDual b) = edist a b
  proof: rfl

@[simp]

中文:
定理 edist_toDual
  条件: (a b : X)
  结论: edist (toDual a) (toDual b) = edist a b
  证明: rfl

@[simp]
-/
theorem edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b :=
  rfl

@[simp]
/--
theorem `edist_ofDual` / 定理 `edist_ofDual`

English:
theorem edist_ofDual
  given: (a b : Xᵒᵈ)
  statement: edist (ofDual a) (ofDual b) = edist a b
  proof: rfl

中文:
定理 edist_ofDual
  条件: (a b : Xᵒᵈ)
  结论: edist (ofDual a) (ofDual b) = edist a b
  证明: rfl
-/
theorem edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b :=
  rfl

end

section

/--
Definition of `WeakPseudoEMetricSpace` / `WeakPseudoEMetricSpace` 的定义

English:
class WeakPseudoEMetricSpace
  extends: EDist α
  axioms and operations (5):
    - edist_self : forall x : α, edist x x = 0
    - edist_comm : forall x y : α, edist x y = edist y x
    - edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z
    - topology_le : (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle).toTopologicalSpace <= τ
    - topology_eq_on_restrict : forall (x : α) (r : Real>=0∞), IsOpen ((Metric.eball x ⊤) ↓inter (Metric.eball x r))

中文:
类 WeakPseudoEMetric空间
  继承: EDist α
  公理与运算 (5 个):
    - edist_self : 对任意 x : α, edist x x = 0
    - edist_comm : 对任意 x y : α, edist x y = edist y x
    - edist_triangle : 对任意 x y z : α, edist x z <= edist x y + edist y z
    - topology_le : (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle).toTopologicalSpace <= τ
    - topology_eq_on_restrict : 对任意 (x : α) (r : 实数>=0∞), 是开集 ((Metric.eball x ⊤) ↓inter (Metric.eball x r))
-/
class WeakPseudoEMetricSpace
    (α : Type u) [τ : TopologicalSpace α] : Type u extends EDist α where
  edist_self : forall x : α, edist x x = 0
  edist_comm : forall x y : α, edist x y = edist y x
  edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z
  /-- The topology on `α` is at most as fine as the topology generated by the `edist`. -/
  topology_le :
    (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle).toTopologicalSpace <= τ
  /-- The ambient topology on `α` matches the `edist` topology on eballs. -/
  topology_eq_on_restrict :
    forall (x : α) (r : Real>=0∞),
    IsOpen ((Metric.eball x ⊤) ↓inter (Metric.eball x r))

@[ext]
/--
theorem `WeakPseudoEMetricSpace.ext` / 定理 `WeakPseudoEMetricSpace.ext`

English:
theorem WeakPseudoEMetricSpace.ext
  proof: by
  cases m; cases m'; congr

中文:
定理 WeakPseudoEMetric空间.ext
  证明: by
  cases m; cases m'; congr
-/
protected theorem WeakPseudoEMetricSpace.ext
    {α : Type*} [TopologicalSpace α] {m m' : WeakPseudoEMetricSpace α}
      (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m; cases m'; congr

/--
Instance `PseudoEMetricSpace.toWeakPseudoEMetricSpace` / 实例 `PseudoEMetricSpace.toWeakPseudoEMetricSpace`

English:
instance PseudoEMetricSpace.toWeakPseudoEMetricSpace
  signature: (α : Type u) [inst : PseudoEMetricSpace α]
  body: edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  topology_le := by rw [uniformSpace_edist]
  topology_eq_on_restrict _ _ := Metric.isOpen_eball.preimage_val

中文:
实例 PseudoEMetric空间.toWeakPseudoEMetricSpace
  签名: (α : 类型u) [inst : PseudoEMetric空间 α]
  定义体: edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  topology_le := by rw [uniformSpace_edist]
  topology_eq_on_restrict _ _ := Metric.isOpen_eball.preimage_val

Depends on / 依赖: edist_self
-/
instance PseudoEMetricSpace.toWeakPseudoEMetricSpace (α : Type u) [inst : PseudoEMetricSpace α] :
    WeakPseudoEMetricSpace α where
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  topology_le := by rw [uniformSpace_edist]
  topology_eq_on_restrict _ _ := Metric.isOpen_eball.preimage_val

/--
Definition of `WeakPseudoEMetricSpace.IsInducing` / `WeakPseudoEMetricSpace.IsInducing` 的定义

English:
abbreviation WeakPseudoEMetricSpace.IsInducing
  signature: {α β : Type*} [e : TopologicalSpace α]
  body: fun x y => edist (f x) (f y)
  edist_self x := edist_self (f x)
  edist_comm x y := edist_comm (f x) (f y)
  edist_triangle x y z := edist_triangle (f x) (f y) (f z)
  topology_le := by
    let hα := PseudoEMetricSpace.ofEDist (fun x y => edist (f x) (f y))
      (fun x => edist_self (f x)) (fun x y

中文:
缩写 WeakPseudoEMetric空间.是Inducing
  签名: {α β : 类型} [e : 拓扑空间 α]
  定义体: fun x y => edist (f x) (f y)
  edist_self x := edist_self (f x)
  edist_comm x y := edist_comm (f x) (f y)
  edist_triangle x y z := edist_triangle (f x) (f y) (f z)
  topology_le := by
    let hα := PseudoEMetricSpace.ofEDist (fun x y => edist (f x) (f y))
      (fun x => edist_self (f x)) (fun x y
-/
abbrev WeakPseudoEMetricSpace.IsInducing {α β : Type*} [e : TopologicalSpace α]
  [n : TopologicalSpace β] {f : α -> β} (hf : IsInducing f) (m : WeakPseudoEMetricSpace β) :
    WeakPseudoEMetricSpace α where
  edist := fun x y => edist (f x) (f y)
  edist_self x := edist_self (f x)
  edist_comm x y := edist_comm (f x) (f y)
  edist_triangle x y z := edist_triangle (f x) (f y) (f z)
  topology_le := by
    let hα := PseudoEMetricSpace.ofEDist (fun x y => edist (f x) (f y))
      (fun x => edist_self (f x)) (fun x y => edist_comm (f x) (f y))
      (fun x y z => edist_triangle (f x) (f y) (f z))
    let hβ := PseudoEMetricSpace.ofEDist m.edist edist_self edist_comm edist_triangle
    rw [(isInducing_iff f).mp hf]
    refine (continuous_le_rng m.topology_le ?_).le_induced
    refine @Continuous.mk α β hα.toUniformSpace.toTopologicalSpace
      hβ.toUniformSpace.toTopologicalSpace f fun s hs => ?_
    rw [isOpen_iff] at hs ⊢
    intro x (hx : f x in s)
    obtain ⟨ε, hε, hεs⟩ := hs (f x) hx
    exact ⟨ε, hε, fun y hy => hεs hy⟩
  topology_eq_on_restrict x r := by
    obtain ⟨u, hu, uy⟩ := m.topology_eq_on_restrict (f x) r
    rw [(isInducing_iff f).mp hf]
    exact ⟨f ⁻¹' u, isOpen_induced hu, by aesop (add simp [Set.ext_iff])⟩

/-- Weak pseudo-emetric space instance on subsets of weak pseudo-emetric spaces -/
instance {α : Type*} {p : α -> Prop} [TopologicalSpace α] [WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (Subtype p) :=
  WeakPseudoEMetricSpace.IsInducing IsInducing.subtypeVal ‹_›

/--
Definition of `WeakEMetricSpace` / `WeakEMetricSpace` 的定义

English:
class WeakEMetricSpace
  extends: WeakPseudoEMetricSpace α
  axioms and operations (1):
    - eq_of_edist_eq_zero : forall {x y : α}, edist x y = 0 -> x = y

中文:
类 WeakEMetric空间
  继承: WeakPseudoEMetric空间 α
  公理与运算 (1 个):
    - eq_of_edist_eq_zero : 对任意 {x y : α}, edist x y = 0 -> x = y
-/
class WeakEMetricSpace
    (α : Type u) [TopologicalSpace α] : Type u extends WeakPseudoEMetricSpace α where
  eq_of_edist_eq_zero : forall {x y : α}, edist x y = 0 -> x = y

@[ext]
/--
theorem `WeakEMetricSpace.ext` / 定理 `WeakEMetricSpace.ext`

English:
theorem WeakEMetricSpace.ext
  statement: {α : Type*} [TopologicalSpace α] {m m' : WeakEMetricSpace α}
  proof: by
  cases m
  cases m'
  congr
  ext1
  assumption

中文:
定理 WeakEMetric空间.ext
  结论: {α : 类型} [拓扑空间 α] {m m' : WeakEMetric空间 α}
  证明: by
  cases m
  cases m'
  congr
  ext1
  assumption
-/
protected theorem WeakEMetricSpace.ext {α : Type*} [TopologicalSpace α] {m m' : WeakEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

/--
Instance `EMetricSpace.toWeakEMetricSpace` / 实例 `EMetricSpace.toWeakEMetricSpace`

English:
instance EMetricSpace.toWeakEMetricSpace
  signature: (α : Type u) [EMetricSpace α]
  body: eq_of_edist_eq_zero

中文:
实例 广义度量空间.toWeakEMetricSpace
  签名: (α : 类型u) [广义度量空间 α]
  定义体: eq_of_edist_eq_zero

Depends on / 依赖: eq_of_edist_eq_zero
-/
instance EMetricSpace.toWeakEMetricSpace (α : Type u) [EMetricSpace α] :
    WeakEMetricSpace α where
  eq_of_edist_eq_zero := eq_of_edist_eq_zero

/--
Definition of `WeakEMetricSpace.induced` / `WeakEMetricSpace.induced` 的定义

English:
abbreviation WeakEMetricSpace.induced
  body: letI := TopologicalSpace.induced f n
  { WeakPseudoEMetricSpace.IsInducing (f := f) {eq_induced := rfl} m.toWeakPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (m.eq_of_edist_eq_zero h) }

中文:
缩写 WeakEMetric空间.induced
  定义体: letI := TopologicalSpace.induced f n
  { WeakPseudoEMetricSpace.IsInducing (f := f) {eq_induced := rfl} m.toWeakPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (m.eq_of_edist_eq_zero h) }

Depends on / 依赖: IsInducing, TopologicalSpace, TopologicalSpace.induced, WeakPseudoEMetricSpace, WeakPseudoEMetricSpace.IsInducing, eq_induced, eq_of_edist_eq_zero, induced, m.eq_of_edist_eq_zero, m.toWeakPseudoEMetricSpace, toWeakPseudoEMetricSpace
-/
abbrev WeakEMetricSpace.induced
  {α β : Type*} [n : TopologicalSpace β]
  {f : α -> β} (hf : Function.Injective f) (m : WeakEMetricSpace β) :
    @WeakEMetricSpace α (TopologicalSpace.induced f n) :=
  letI := TopologicalSpace.induced f n
  { WeakPseudoEMetricSpace.IsInducing (f := f) {eq_induced := rfl} m.toWeakPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (m.eq_of_edist_eq_zero h) }

/-- `WeakEMetricSpace` instance on subsets of emetric spaces -/
instance {α : Type*} {p : α -> Prop} [TopologicalSpace α] [WeakEMetricSpace α] :
    WeakEMetricSpace (Subtype p) :=
  WeakEMetricSpace.induced Subtype.coe_injective ‹_›

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: X] [WeakPseudoEMetricSpace X] : WeakPseudoEMetricSpace Xᵒᵈ
  body: ‹WeakPseudoEMetricSpace X›

中文:
实例 [拓扑空间
  签名: X] [WeakPseudoEMetric空间 X] : WeakPseudoEMetric空间 Xᵒᵈ
  定义体: ‹WeakPseudoEMetricSpace X›

Depends on / 依赖: WeakPseudoEMetricSpace
-/
instance [TopologicalSpace X] [WeakPseudoEMetricSpace X] : WeakPseudoEMetricSpace Xᵒᵈ :=
  ‹WeakPseudoEMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: X] [WeakEMetricSpace X] : WeakEMetricSpace Xᵒᵈ
  body: ‹WeakEMetricSpace X›

中文:
实例 [拓扑空间
  签名: X] [WeakEMetric空间 X] : WeakEMetric空间 Xᵒᵈ
  定义体: ‹WeakEMetricSpace X›

Depends on / 依赖: WeakEMetricSpace
-/
instance [TopologicalSpace X] [WeakEMetricSpace X] : WeakEMetricSpace Xᵒᵈ :=
  ‹WeakEMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : PseudoEMetricSpace Xᵒᵈ
  body: ‹PseudoEMetricSpace X›

中文:
实例 [PseudoEMetric空间
  签名: X] : PseudoEMetric空间 Xᵒᵈ
  定义体: ‹PseudoEMetricSpace X›

Depends on / 依赖: PseudoEMetricSpace
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ :=
  ‹PseudoEMetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EMetricSpace
  signature: X] : EMetricSpace Xᵒᵈ
  body: ‹EMetricSpace X›

中文:
实例 [广义度量空间
  签名: X] : 广义度量空间 Xᵒᵈ
  定义体: ‹EMetricSpace X›
-/
instance [EMetricSpace X] : EMetricSpace Xᵒᵈ :=
  ‹EMetricSpace X›
