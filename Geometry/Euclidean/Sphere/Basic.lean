/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Spheres

This file defines and proves basic results about spheres and cospherical sets of points in
Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.Sphere` bundles a `center` and a `radius`.

* `EuclideanGeometry.Sphere.IsDiameter` is the property of two points being the two endpoints
  of a diameter of a sphere.

* `EuclideanGeometry.Sphere.ofDiameter` constructs the sphere on a given diameter.

* `EuclideanGeometry.Cospherical` is the property of a set of points being equidistant from some
  point.

* `EuclideanGeometry.Concyclic` is the property of a set of points being cospherical and
  coplanar.

-/

@[expose] public section


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} (P : Type*)

open Module

/-- A `Sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext]
/-
**EuclideanGeometry.Sphere** 是 Mathlib 中的一个归纳类型，位于命名空间 `EuclideanGeometry`。
形式化陈述：(P : Type u_2) → [MetricSpace P] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Sphere P` bundles a `center` and `radius`. This definition does not require t
he radius to
be positive; that should be given as a hypothesis to lemmas that require it.
-/
structure Sphere [MetricSpace P] where
  /-- center of this sphere -/
  center : P
  /-- radius of the sphere; not required to be positive -/
  radius : ℝ

variable {P}

section MetricSpace

variable [MetricSpace P]

/-
**EuclideanGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty P] : Nonempty (Sphere P) :=
  ⟨⟨Classical.arbitrary P, 0⟩⟩
/-
**EuclideanGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Sphere P) (Set P) :=
  ⟨fun s => Metric.sphere s.center s.radius⟩
/-
**EuclideanGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership P (Sphere P) :=
  ⟨fun s p => p ∈ (s : Set P)⟩
/-
**EuclideanGeometry.Sphere.mk_center** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] (c : P) (r : ℝ), { center := c, ra
dius := r }.center = c
参数：c : P；r : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sphere.mk_center (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).center = c :=
  rfl
/-
**EuclideanGeometry.Sphere.mk_radius** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] (c : P) (r : ℝ), { center := c, ra
dius := r }.radius = r
参数：c : P；r : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sphere.mk_radius (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).radius = r :=
  rfl

@[simp]
/-
**EuclideanGeometry.Sphere.mk_center_radius** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] (s : EuclideanGeometry.Sphere P), 
{ center := s.center, radius := s.radius } = s
参数：s : EuclideanGeometry.Sphere P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
-/
theorem Sphere.mk_center_radius (s : Sphere P) : (⟨s.center, s.radius⟩ : Sphere P) = s := by
  ext <;> rfl

@[simp]
/-
**EuclideanGeometry.Sphere.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.S
phere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] (c : P) (r : ℝ),   Metric.sphere {
 center := c, radius := r }.center { center := c, radius := r }.radius = Metric.
sphere c r
参数：c : P；r : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sphere.coe_mk (c : P) (r : ℝ) : ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r :=
  rfl

-- simp-normal form is `Sphere.mem_coe'`
/-
**EuclideanGeometry.Sphere.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.
Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {p : P} {s : EuclideanGeometry.Sph
ere P},   p ∈ Metric.sphere s.center s.radius ↔ p ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Sphere.mem_coe {p : P} {s : Sphere P} : p ∈ (s : Set P) ↔ p ∈ s :=
  Iff.rfl

@[simp]
/-
**EuclideanGeometry.Sphere.mem_coe'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {p : P} {s : EuclideanGeometry.Sph
ere P}, dist p s.center = s.radius ↔ p ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Sphere.mem_coe' {p : P} {s : Sphere P} : dist p s.center = s.radius ↔ p ∈ s :=
  Iff.rfl
/-
**EuclideanGeometry.mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：mem_sphere {p : P} {s : Sphere P} : p in s ↔ dist p s.center = s.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sphere {p : P} {s : Sphere P} : p ∈ s ↔ dist p s.center = s.radius :=
  Iff.rfl
/-
**EuclideanGeometry.mem_sphere'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：mem_sphere' {p : P} {s : Sphere P} : p in s ↔ dist s.center p = s.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_sphere'`：mem_sphere' : y in sphere x ε ↔ dist x y = ε
-/
theorem mem_sphere' {p : P} {s : Sphere P} : p ∈ s ↔ dist s.center p = s.radius :=
  Metric.mem_sphere'
/-
**EuclideanGeometry.subset_sphere** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：subset_sphere {ps : Set P} {s : Sphere P} : ps subseteq s ↔ forall p in ps
, p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_sphere {ps : Set P} {s : Sphere P} : ps ⊆ s ↔ ∀ p ∈ ps, p ∈ s :=
  Iff.rfl
/-
**EuclideanGeometry.dist_of_mem_subset_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
形式化陈述：dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p in p
s) (hps : ps subseteq (s : Set P)) : dist p s.center = s.radius
参数：hp : p in ps；hps : ps subseteq (s : Set P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `EuclideanGeometry.Sphere.mem_coe`：∀ {P : Type u_2} [inst : MetricSpace P
] {p : P} {s : EuclideanGeometry.Sphere P},   p ∈ Metric.sphere s.center s.radiu
s ↔ p ∈ s
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
-/
theorem dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p ∈ ps)
    (hps : ps ⊆ (s : Set P)) : dist p s.center = s.radius :=
  mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))
/-
**EuclideanGeometry.dist_of_mem_subset_mk_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : Real} (hp : p in 
ps) (hps : ps subseteq ↑(⟨c, r⟩ : Sphere P)) : dist p c = r
参数：hp : p in ps；hps : ps subseteq ↑(⟨c, r⟩ : Sphere P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_of_mem_subset_sphere`：dist_of_mem_subset_sphere {
p : P} {ps : Set P} {s : Sphere P} (hp : p in ps) (hps : ps subseteq (s : Set P)
) : dist p s.center = s.radius
-/
theorem dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : ℝ} (hp : p ∈ ps)
    (hps : ps ⊆ ↑(⟨c, r⟩ : Sphere P)) : dist p c = r :=
  dist_of_mem_subset_sphere hp hps
/-
**EuclideanGeometry.Sphere.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.S
phere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere 
P},   s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `EuclideanGeometry.Sphere.ext_iff`：∀ {P : Type u_2} {inst : MetricSpace P
} {x y : EuclideanGeometry.Sphere P},   x = y ↔ x.center = y.center ∧ x.radius =
 y.radius
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Sphere.ne_iff {s₁ s₂ : Sphere P} :
    s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius := by
  rw [← not_and_or, ← Sphere.ext_iff]
/-
**EuclideanGeometry.Sphere.center_eq_iff_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere 
P} {p : P},   p ∈ s₁ → p ∈ s₂ → (s₁.center = s₂.center ↔ s₁ = s₂)
参数：s₁.center = s₂.center ↔ s₁ = s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
-/
theorem Sphere.center_eq_iff_eq_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center = s₂.center ↔ s₁ = s₂ := by
  refine ⟨fun h => Sphere.ext h ?_, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁, ← hs₂, h]
/-
**EuclideanGeometry.Sphere.center_ne_iff_ne_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere 
P} {p : P},   p ∈ s₁ → p ∈ s₂ → (s₁.center ≠ s₂.center ↔ s₁ ≠ s₂)
参数：s₁.center ≠ s₂.center ↔ s₁ ≠ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EuclideanGeometry.Sphere.center_eq_iff_eq_of_mem`：∀ {P : Type u_2} [inst
 : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   p ∈ s₁ → p ∈ s
₂ → (s₁.center = s₂.center ↔ s₁ = s₂)
-/
theorem Sphere.center_ne_iff_ne_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center ≠ s₂.center ↔ s₁ ≠ s₂ :=
  (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not
/-
**EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ :
 p₁ in s) (hp₂ : p₂ in s) : dist p₁ s.center = dist p₂ s.center
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
-/
theorem dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist p₁ s.center = dist p₂ s.center := by
  rw [mem_sphere.1 hp₁, mem_sphere.1 hp₂]
/-
**EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ 
: p₁ in s) (hp₂ : p₂ in s) : dist s.center p₁ = dist s.center p₂
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
-/
theorem dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist s.center p₁ = dist s.center p₂ := by
  rw [mem_sphere'.1 hp₁, mem_sphere'.1 hp₂]
/-
**EuclideanGeometry.Sphere.radius_nonneg_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s : EuclideanGeometry.Sphere P} {
p : P}, p ∈ s → 0 ≤ s.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.nonneg_of_mem_sphere`：nonneg_of_mem_sphere (hy : y in sphere x ε)
 : 0 <= ε
-/
lemma Sphere.radius_nonneg_of_mem {s : Sphere P} {p : P} (h : p ∈ s) : 0 ≤ s.radius :=
  Metric.nonneg_of_mem_sphere h
/-
**EuclideanGeometry.Sphere.center_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s : EuclideanGeometry.Sphere P}, 
s.center ∈ s ↔ s.radius = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Sphere.center_mem_iff {s : Sphere P} : s.center ∈ s ↔ s.radius = 0 := by
  simp [mem_sphere, eq_comm]

/-- A point of a sphere that differs from another point of the sphere is not its center. -/
/-
**EuclideanGeometry.Sphere.ne_center_of_mem_of_mem_of_ne** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {s : EuclideanGeometry.Sphere P} {
p q : P}, p ∈ s → q ∈ s → p ≠ q → p ≠ s.center
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point of a sphere that differs from another point of the sphere is not its cen
ter.
-/
lemma Sphere.ne_center_of_mem_of_mem_of_ne {s : Sphere P} {p q : P}
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) : p ≠ s.center := by
  grind [dist_eq_zero, mem_sphere']

/-- A set of points is cospherical if they are equidistant from some
point. In two dimensions, this is the same thing as being
concyclic. -/
/-
**EuclideanGeometry.Cospherical** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeometry`。
形式化陈述：Cospherical (ps : Set P) : Prop
参数：ps : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points is cospherical if they are equidistant from some
point. In two dimensions, this is the same thing as being
concyclic.
-/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius

/-- The definition of `Cospherical`. -/
/-
**EuclideanGeometry.cospherical_def** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：cospherical_def (ps : Set P) : Cospherical ps ↔ exists (center : P) (radiu
s : Real), forall p in ps, dist p center = radius
参数：ps : Set P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The definition of `Cospherical`.
-/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
  Iff.rfl

/-- A set of points is cospherical if and only if they lie in some sphere. -/
/-
**EuclideanGeometry.cospherical_iff_exists_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry`。
形式化陈述：cospherical_iff_exists_sphere {ps : Set P} : Cospherical ps ↔ exists s : S
phere P, ps subseteq (s : Set P)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points is cospherical if and only if they lie in some sphere.
-/
theorem cospherical_iff_exists_sphere {ps : Set P} :
    Cospherical ps ↔ ∃ s : Sphere P, ps ⊆ (s : Set P) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩

/-- The set of points in a sphere is cospherical. -/
/-
**EuclideanGeometry.Sphere.cospherical** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try.Sphere`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] (s : EuclideanGeometry.Sphere P), 
  EuclideanGeometry.Cospherical (Metric.sphere s.center s.radius)
参数：s : EuclideanGeometry.Sphere P；Metric.sphere s.center s.radius。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.cospherical_iff_exists_sphere`：cospherical_iff_exists_
sphere {ps : Set P} : Cospherical ps ↔ exists s : Sphere P, ps subseteq (s : Set
 P)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The set of points in a sphere is cospherical.
-/
theorem Sphere.cospherical (s : Sphere P) : Cospherical (s : Set P) :=
  cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩

/-- A subset of a cospherical set is cospherical. -/
/-
**EuclideanGeometry.Cospherical.subset** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try.Cospherical`。
形式化陈述：∀ {P : Type u_2} [inst : MetricSpace P] {ps₁ ps₂ : Set P},   ps₁ ⊆ ps₂ → E
uclideanGeometry.Cospherical ps₂ → EuclideanGeometry.Cospherical ps₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a cospherical set is cospherical.
-/
theorem Cospherical.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (hc : Cospherical ps₂) :
    Cospherical ps₁ := by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩

/-- The empty set is cospherical. -/
/-
**EuclideanGeometry.cospherical_empty** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
形式化陈述：cospherical_empty [Nonempty P] : Cospherical (∅ : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty set is cospherical.
-/
theorem cospherical_empty [Nonempty P] : Cospherical (∅ : Set P) :=
  let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun _ => False.elim⟩

/-- A single point is cospherical. -/
/-
**EuclideanGeometry.cospherical_singleton** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：cospherical_singleton (p : P) : Cospherical ({p} : Set P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0

--- 原说明 ---
A single point is cospherical.
-/
theorem cospherical_singleton (p : P) : Cospherical ({p} : Set P) := by
  use p
  simp

/-- If `ps` is cospherical, then any of its isometric images is cospherical. -/
/-
**EuclideanGeometry._root_.Isometry.cospherical** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ps` is cospherical, then any of its isometric images is cospherical.
-/
theorem _root_.Isometry.cospherical {E F : Type*} [MetricSpace E] [MetricSpace F] {f : E → F}
    (hf : Isometry f) {ps : Set E} (hps : Cospherical ps) : Cospherical (f '' ps) := by
  rcases hps with ⟨c, r, hc⟩
  refine ⟨f c, r, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [hf.dist_eq, hc p hp]

end MetricSpace

section NormedSpace

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- If a set of points is cospherical, then its image under the inclusion of any affine subspace
containing it is cospherical. -/
/-
**EuclideanGeometry.Cospherical.inclusion** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {S₁ S₂ 
: AffineSubspace ℝ P} [inst_4 : Nonempty ↥S₁] {ps : Set ↥S₁},   EuclideanGeometr
y.Cospherical ps →     ∀ (hS : S₁ ≤ S₂), EuclideanGeometry.Cospherical (⇑(Affine
Subspace.inclusion hS) '' ps)
参数：hS : S₁ ≤ S₂；⇑(AffineSubspace.inclusion hS) '' ps。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.cospherical`：∀ {E : Type u_3} {F : Type u_4} [inst : MetricSpac
e E] [inst_1 : MetricSpace F] {f : E → F},   Isometry f → ∀ {ps : Set E}, Euclid
eanGeometr…
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…

--- 原说明 ---
If a set of points is cospherical, then its image under the inclusion of any aff
ine subspace
containing it is cospherical.
-/
theorem Cospherical.inclusion {S₁ S₂ : AffineSubspace ℝ P} [Nonempty S₁] {ps : Set S₁}
    (hps : Cospherical ps) (hS : S₁ ≤ S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) := by
  refine Isometry.cospherical ?_ hps
  exact S₁.subtypeₐᵢ.isometry

/-- If a set of points in an affine subspace is cospherical, then its image under the coercion
to the ambient space is cospherical. -/
/-
**EuclideanGeometry.Cospherical.subtype_val** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {S : Af
fineSubspace ℝ P} [Nonempty ↥S] {ps : Set ↥S},   EuclideanGeometry.Cospherical p
s → EuclideanGeometry.Cospherical (Subtype.val '' ps)
参数：Subtype.val '' ps。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.cospherical`：∀ {E : Type u_3} {F : Type u_4} [inst : MetricSpac
e E] [inst_1 : MetricSpace F] {f : E → F},   Isometry f → ∀ {ps : Set E}, Euclid
eanGeometr…
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…

--- 原说明 ---
If a set of points in an affine subspace is cospherical, then its image under th
e coercion
to the ambient space is cospherical.
-/
theorem Cospherical.subtype_val {S : AffineSubspace ℝ P} [Nonempty S] {ps : Set S}
    (hps : Cospherical ps) : Cospherical (Subtype.val '' ps) :=
  Isometry.cospherical S.subtypeₐᵢ.isometry hps

omit [NormedSpace ℝ V] in
/-- For a point on a sphere, the norm of its displacement from the center equals the radius. -/
/-
**EuclideanGeometry.norm_vsub_center_eq_radius** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：norm_vsub_center_eq_radius {s : Sphere P} {p : P} (hp : p in s) : ‖p -ᵥ s.
center‖ = s.radius
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius

--- 原说明 ---
For a point on a sphere, the norm of its displacement from the center equals the
 radius.
-/
theorem norm_vsub_center_eq_radius {s : Sphere P} {p : P} (hp : p ∈ s) :
    ‖p -ᵥ s.center‖ = s.radius := by
  rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp
/-
**EuclideanGeometry.Sphere.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeom
etry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [NormedSpace
 ℝ V] [inst_2 : MetricSpace P]   [NormedAddTorsor V P] [Nontrivial V] {s : Eucli
deanGeometry.Sphere P},   (Metric.sphere s.center s.radius).Nonempty ↔ 0 ≤ s.rad
ius
参数：Metric.sphere s.center s.radius。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedSpace.sphere_nonempty`：NormedSpace.sphere_nonempty {x : E} {r : Re
al} : (sphere x r).Nonempty ↔ 0 <= r
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma Sphere.nonempty_iff [Nontrivial V] {s : Sphere P} : (s : Set P).Nonempty ↔ 0 ≤ s.radius := by
  refine ⟨fun ⟨p, hp⟩ ↦ radius_nonneg_of_mem hp, fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : V)) (r := s.radius)).2 h
  refine ⟨v +ᵥ s.center, ?_⟩
  simpa [mem_sphere] using hv

include V in
/-- Two points are cospherical. -/
/-
**EuclideanGeometry.cospherical_pair** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：cospherical_pair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_midpoint_left`：dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁
 p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `dist_midpoint_right`：dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 
p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂

--- 原说明 ---
Two points are cospherical.
-/
theorem cospherical_pair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) :=
  ⟨midpoint ℝ p₁ p₂, ‖(2 : ℝ)‖⁻¹ * dist p₁ p₂, by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left (𝕜 := ℝ)]
    · rw [dist_comm, dist_midpoint_right (𝕜 := ℝ)]⟩

/-- A set of points is concyclic if it is cospherical and coplanar. (Most results are stated
directly in terms of `Cospherical` instead of using `Concyclic`.) -/
/-
**EuclideanGeometry.Concyclic** 是 Mathlib 中的一个归纳类型，位于命名空间 `EuclideanGeometry`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] → [N
ormedSpace ℝ V] → [inst_2 : MetricSpace P] → [NormedAddTorsor V P] → Set P → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points is concyclic if it is cospherical and coplanar. (Most results ar
e stated
directly in terms of `Cospherical` instead of using `Concyclic`.)
-/
structure Concyclic (ps : Set P) : Prop where
  Cospherical : Cospherical ps
  Coplanar : Coplanar ℝ ps

/-- A subset of a concyclic set is concyclic. -/
/-
**EuclideanGeometry.Concyclic.subset** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y.Concyclic`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {ps₁ ps
₂ : Set P},   ps₁ ⊆ ps₂ → EuclideanGeometry.Concyclic ps₂ → EuclideanGeometry.Co
ncyclic ps₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Cospherical.subset`：∀ {P : Type u_2} [inst : MetricSpa
ce P] {ps₁ ps₂ : Set P},   ps₁ ⊆ ps₂ → EuclideanGeometry.Cospherical ps₂ → Eucli
deanGeometry.Cospherical p…
· 使用定理 `EuclideanGeometry.Concyclic.Cospherical`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAddTorso…
· 使用定理 `Coplanar.subset`：Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (
h : Coplanar k s₂) : Coplanar k s₁
· 使用定理 `EuclideanGeometry.Concyclic.Coplanar`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAddTorso…

--- 原说明 ---
A subset of a concyclic set is concyclic.
-/
theorem Concyclic.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (h : Concyclic ps₂) : Concyclic ps₁ :=
  ⟨h.1.subset hs, h.2.subset hs⟩

/-- The empty set is concyclic. -/
/-
**EuclideanGeometry.concyclic_empty** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：concyclic_empty : Concyclic (∅ : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.cospherical_empty`：cospherical_empty [Nonempty P] : Co
spherical (∅ : Set P)
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `coplanar_empty`：coplanar_empty : Coplanar k (∅ : Set P)

--- 原说明 ---
The empty set is concyclic.
-/
theorem concyclic_empty : Concyclic (∅ : Set P) :=
  ⟨cospherical_empty, coplanar_empty ℝ P⟩

/-- A single point is concyclic. -/
/-
**EuclideanGeometry.concyclic_singleton** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeom
etry`。
形式化陈述：concyclic_singleton (p : P) : Concyclic ({p} : Set P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.cospherical_singleton`：cospherical_singleton (p : P) :
 Cospherical ({p} : Set P)
· 使用定理 `coplanar_singleton`：coplanar_singleton (p : P) : Coplanar k ({p} : Set P
)

--- 原说明 ---
A single point is concyclic.
-/
theorem concyclic_singleton (p : P) : Concyclic ({p} : Set P) :=
  ⟨cospherical_singleton p, coplanar_singleton ℝ p⟩

/-- Two points are concyclic. -/
/-
**EuclideanGeometry.concyclic_pair** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`
。
形式化陈述：concyclic_pair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.cospherical_pair`：cospherical_pair (p₁ p₂ : P) : Cosph
erical ({p₁, p₂} : Set P)
· 使用定理 `coplanar_pair`：coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P)

--- 原说明 ---
Two points are concyclic.
-/
theorem concyclic_pair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P) :=
  ⟨cospherical_pair p₁ p₂, coplanar_pair ℝ p₁ p₂⟩

namespace Sphere

/-- `s.IsDiameter p₁ p₂` says that `p₁` and `p₂` are the two endpoints of a diameter of `s`. -/
/-
**EuclideanGeometry.Sphere.IsDiameter** 是 Mathlib 中的一个归纳类型，位于命名空间 `EuclideanGeom
etry.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [NormedSpace ℝ V] → [inst_2 : MetricSpace P] → [NormedAddTorsor V P] → Eucli
deanGeometry.Sphere P → P → P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.IsDiameter p₁ p₂` says that `p₁` and `p₂` are the two endpoints of a diameter
 of `s`.
-/
structure IsDiameter (s : Sphere P) (p₁ p₂ : P) : Prop where
  left_mem : p₁ ∈ s
  midpoint_eq_center : midpoint ℝ p₁ p₂ = s.center

variable {s : Sphere P} {p₁ p₂ p₃ : P}
/-
**EuclideanGeometry.Sphere.IsDiameter.right_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P}, s.IsDiameter p₁ p₂ → p₂ ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `dist_left_midpoint_eq_dist_right_midpoint`：dist_left_midpoint_eq_dist_ri
ght_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p
₂)
-/
lemma IsDiameter.right_mem (h : s.IsDiameter p₁ p₂) : p₂ ∈ s := by
  rw [mem_sphere, ← mem_sphere.1 h.left_mem, ← h.midpoint_eq_center,
    dist_left_midpoint_eq_dist_right_midpoint]
/-
**EuclideanGeometry.Sphere.IsDiameter.symm** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P}, s.IsDiameter p₁ p₂ → s.IsDiameter p₂ p₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.right_mem`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAddTorso…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
-/
protected lemma IsDiameter.symm (h : s.IsDiameter p₁ p₂) : s.IsDiameter p₂ p₁ :=
  ⟨h.right_mem, midpoint_comm (R := ℝ) p₁ p₂ ▸ h.midpoint_eq_center⟩
/-
**EuclideanGeometry.Sphere.isDiameter_comm** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanG
eometry.Sphere`。
形式化陈述：isDiameter_comm : s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.symm`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAddTorso…
-/
lemma isDiameter_comm : s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁ :=
  ⟨IsDiameter.symm, IsDiameter.symm⟩
/-
**EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_midpoint_eq_center** 是 Ma
thlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_left_mem_and_midpoint_eq_center : s.IsDiameter p₁ p₂ ↔ p₁ i
n s ∧ midpoint Real p₁ p₂ = s.center
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isDiameter_iff_left_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ midpoint ℝ p₁ p₂ = s.center :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
/-
**EuclideanGeometry.Sphere.isDiameter_iff_right_mem_and_midpoint_eq_center** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_right_mem_and_midpoint_eq_center : s.IsDiameter p₁ p₂ ↔ p₂ 
in s ∧ midpoint Real p₁ p₂ = s.center
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.right_mem`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.symm`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAddTorso…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
-/
lemma isDiameter_iff_right_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₂ ∈ s ∧ midpoint ℝ p₁ p₂ = s.center :=
  ⟨fun h ↦ ⟨h.right_mem, h.2⟩, fun h ↦ IsDiameter.symm ⟨h.1, midpoint_comm (R := ℝ) p₁ p₂ ▸ h.2⟩⟩
/-
**EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_left** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → (Equiv.pointReflec
tion s.center) p₁ = p₂
参数：Equiv.pointReflection s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `Equiv.pointReflection_midpoint_left`：Equiv.pointReflection_midpoint_left
 (x y : P) : (Equiv.pointReflection (midpoint R x y)) x = y
-/
lemma IsDiameter.pointReflection_center_left (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₁ = p₂ := by
  rw [← h.midpoint_eq_center, Equiv.pointReflection_midpoint_left]
/-
**EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → (Equiv.pointReflec
tion s.center) p₂ = p₁
参数：Equiv.pointReflection s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `Equiv.pointReflection_midpoint_right`：Equiv.pointReflection_midpoint_rig
ht (x y : P) : (Equiv.pointReflection (midpoint R x y)) y = x
-/
lemma IsDiameter.pointReflection_center_right (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₂ = p₁ := by
  rw [← h.midpoint_eq_center, Equiv.pointReflection_midpoint_right]
/-
**EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_le
ft** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_left_mem_and_pointReflection_center_left : s.IsDiameter p₁ 
p₂ ↔ p₁ in s ∧ Equiv.pointReflection s.center p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_left`：∀ {V : 
Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `midpoint_pointReflection_right`：midpoint_pointReflection_right (x y : P)
 : midpoint R y (Equiv.pointReflection x y) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isDiameter_iff_left_mem_and_pointReflection_center_left :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ Equiv.pointReflection s.center p₁ = p₂ :=
  ⟨fun h ↦ ⟨h.1, h.pointReflection_center_left⟩, fun h ↦ ⟨h.1, by simp [← h.2]⟩⟩
/-
**EuclideanGeometry.Sphere.isDiameter_iff_right_mem_and_pointReflection_center_r
ight** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_right_mem_and_pointReflection_center_right : s.IsDiameter p
₁ p₂ ↔ p₂ in s ∧ Equiv.pointReflection s.center p₂ = p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_comm`：isDiameter_comm : s.IsDiameter
 p₁ p₂ ↔ s.IsDiameter p₂ p₁
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_cen
ter_left`：isDiameter_iff_left_mem_and_pointReflection_center_left : s.IsDiameter
 p₁ p₂ ↔ p₁ in s ∧ Equiv.pointReflection s.center p₁ = p₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isDiameter_iff_right_mem_and_pointReflection_center_right :
    s.IsDiameter p₁ p₂ ↔ p₂ ∈ s ∧ Equiv.pointReflection s.center p₂ = p₁ := by
  rw [isDiameter_comm, isDiameter_iff_left_mem_and_pointReflection_center_left]
/-
**EuclideanGeometry.Sphere.IsDiameter.right_eq_of_isDiameter** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ p₃ : P},   s.IsDiameter p₁ p₂ → s.IsDiameter p₁
 p₃ → p₂ = p₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_left`：∀ {V : 
Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
-/
lemma IsDiameter.right_eq_of_isDiameter (h₁₂ : s.IsDiameter p₁ p₂) (h₁₃ : s.IsDiameter p₁ p₃) :
    p₂ = p₃ := by
  rw [← h₁₂.pointReflection_center_left, ← h₁₃.pointReflection_center_left]
/-
**EuclideanGeometry.Sphere.IsDiameter.left_eq_of_isDiameter** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ p₃ : P},   s.IsDiameter p₁ p₃ → s.IsDiameter p₂
 p₃ → p₁ = p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right`：∀ {V :
 Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
-/
lemma IsDiameter.left_eq_of_isDiameter (h₁₃ : s.IsDiameter p₁ p₃) (h₂₃ : s.IsDiameter p₂ p₃) :
    p₁ = p₂ := by
  rw [← h₁₃.pointReflection_center_right, ← h₂₃.pointReflection_center_right]
/-
**EuclideanGeometry.Sphere.IsDiameter.dist_left_right** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → dist p₁ p₂ = 2 * s
.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsDiameter.dist_left_right (h : s.IsDiameter p₁ p₂) : dist p₁ p₂ = 2 * s.radius := by
  rw [← mem_sphere.1 h.left_mem, ← h.midpoint_eq_center, dist_left_midpoint]
  simp
/-
**EuclideanGeometry.Sphere.IsDiameter.dist_left_right_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → dist p₁ p₂ / 2 = s
.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.dist_left_right`：∀ {V : Type u_1} {P
 : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsDiameter.dist_left_right_div_two (h : s.IsDiameter p₁ p₂) :
    (dist p₁ p₂) / 2 = s.radius := by
  simp [h.dist_left_right]
/-
**EuclideanGeometry.Sphere.IsDiameter.left_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → (p₁ = p₂ ↔ s.radiu
s = 0)
参数：p₁ = p₂ ↔ s.radius = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.dist_left_right`：∀ {V : Type u_1} {P
 : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsDiameter.left_eq_right_iff (h : s.IsDiameter p₁ p₂) : p₁ = p₂ ↔ s.radius = 0 := by
  rw [← dist_eq_zero, h.dist_left_right]
  simp
/-
**EuclideanGeometry.Sphere.IsDiameter.left_ne_right_iff_radius_ne_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → (p₁ ≠ p₂ ↔ s.radiu
s ≠ 0)
参数：p₁ ≠ p₂ ↔ s.radius ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_eq_right_iff`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAddTorso…
-/
lemma IsDiameter.left_ne_right_iff_radius_ne_zero (h : s.IsDiameter p₁ p₂) :
    p₁ ≠ p₂ ↔ s.radius ≠ 0 :=
  h.left_eq_right_iff.not
/-
**EuclideanGeometry.Sphere.IsDiameter.left_ne_right_iff_radius_pos** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → (p₁ ≠ p₂ ↔ 0 < s.r
adius)
参数：p₁ ≠ p₂ ↔ 0 < s.radius。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_ne_right_iff_radius_ne_zero`：∀ 
{V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpac
e ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsDiameter.left_ne_right_iff_radius_pos (h : s.IsDiameter p₁ p₂) :
    p₁ ≠ p₂ ↔ 0 < s.radius := by
  rw [h.left_ne_right_iff_radius_ne_zero, lt_iff_le_and_ne]
  simp [radius_nonneg_of_mem h.left_mem, eq_comm]
/-
**EuclideanGeometry.Sphere.IsDiameter.wbtw** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → Wbtw ℝ p₁ s.center
 p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `wbtw_midpoint`：wbtw_midpoint (x y : P) : Wbtw R x (midpoint R x y) y
-/
protected lemma IsDiameter.wbtw (h : s.IsDiameter p₁ p₂) : Wbtw ℝ p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact wbtw_midpoint _ _ _
/-
**EuclideanGeometry.Sphere.IsDiameter.sbtw** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → s.radius ≠ 0 → Sbt
w ℝ p₁ s.center p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `sbtw_midpoint_of_ne`：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R
 x (midpoint R x y) y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_ne_right_iff_radius_ne_zero`：∀ 
{V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpac
e ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
-/
protected lemma IsDiameter.sbtw (h : s.IsDiameter p₁ p₂) (hr : s.radius ≠ 0) :
    Sbtw ℝ p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact sbtw_midpoint_of_ne _ (h.left_ne_right_iff_radius_ne_zero.2 hr)

/-- Construct the sphere with the given diameter. -/
/-
**EuclideanGeometry.Sphere.ofDiameter** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeomet
ry.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [NormedSpace ℝ V] → [inst_2 : MetricSpace P] → [NormedAddTorsor V P] → P → P
 → EuclideanGeometry.Sphere P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the sphere with the given diameter.
-/
protected def ofDiameter (p₁ p₂ : P) : Sphere P :=
  ⟨midpoint ℝ p₁ p₂, (dist p₁ p₂) / 2⟩
/-
**EuclideanGeometry.Sphere.isDiameter_ofDiameter** 是 Mathlib 中的一个引理，位于命名空间 `Eucl
ideanGeometry.Sphere`。
形式化陈述：isDiameter_ofDiameter (p₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p
₁ p₂
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma isDiameter_ofDiameter (p₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂ :=
  ⟨by simp [Sphere.ofDiameter, mem_sphere, inv_mul_eq_div], rfl⟩
/-
**EuclideanGeometry.Sphere.IsDiameter.ofDiameter_eq** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry.Sphere.IsDiameter`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : No
rmedSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {s : Eu
clideanGeometry.Sphere P} {p₁ p₂ : P},   s.IsDiameter p₁ p₂ → EuclideanGeometry.
Sphere.ofDiameter p₁ p₂ = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.dist_left_right_div_two`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAddTorso…
-/
lemma IsDiameter.ofDiameter_eq (h : s.IsDiameter p₁ p₂) : .ofDiameter p₁ p₂ = s := by
  ext
  · simp [Sphere.ofDiameter, h.midpoint_eq_center]
  · simp [Sphere.ofDiameter, ← h.dist_left_right_div_two]
/-
**EuclideanGeometry.Sphere.isDiameter_iff_ofDiameter_eq** 是 Mathlib 中的一个引理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_ofDiameter_eq : s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.ofDiameter_eq`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAddTorso…
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_ofDiameter`：isDiameter_ofDiameter (p
₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂
-/
lemma isDiameter_iff_ofDiameter_eq : s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s :=
  ⟨IsDiameter.ofDiameter_eq, by rintro rfl; exact isDiameter_ofDiameter _ _⟩

end Sphere

end NormedSpace

section EuclideanSpace

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- A set of points in an affine subspace is cospherical if and only if its image in the ambient
space is cospherical. -/
@[simp]
/-
**EuclideanGeometry.Cospherical.subtype_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
S : AffineSubspace ℝ P} [Nonempty ↥S] [S.direction.HasOrthogonalProjection]   {p
s : Set ↥S}, EuclideanGeometry.Cospherical (Subtype.val '' ps) ↔ EuclideanGeomet
ry.Cospherical ps
参数：Subtype.val '' ps。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `EuclideanGeometry.cospherical_empty`：cospherical_empty [Nonempty P] : Co
spherical (∅ : Set P)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq`：dist_eq_iff_
dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.
HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (h…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `EuclideanGeometry.Cospherical.subtype_val`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAddTorso…

--- 原说明 ---
A set of points in an affine subspace is cospherical if and only if its image in
 the ambient
space is cospherical.
-/
theorem Cospherical.subtype_val_iff {S : AffineSubspace ℝ P} [Nonempty S]
    [S.direction.HasOrthogonalProjection] {ps : Set S} :
    Cospherical (Subtype.val '' ps) ↔ Cospherical ps := by
  refine ⟨fun h => ?_, Cospherical.subtype_val⟩
  rcases ps.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact cospherical_empty
  · rcases h with ⟨c, r, hr⟩
    let c' : S := orthogonalProjection S c
    refine ⟨c', dist p₀ c', fun p hp => ?_⟩
    have hp_dist : dist (p : P) c = r := by grind
    have hp₀_dist : dist (p₀ : P) c = r := by grind
    have hpp₀ : dist (p : P) (c : P) = dist (p₀ : P) (c : P) := hp_dist.trans hp₀_dist.symm
    exact (dist_eq_iff_dist_orthogonalProjection_eq (s := S) (p₃ := c) p.2 p₀.2).1 hpp₀

/-- A set of points is cospherical in an affine subspace `S₁` if and only if its image under the
inclusion into a larger affine subspace `S₂` is cospherical. -/
/-
**EuclideanGeometry.Cospherical.inclusion_iff** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
S₁ S₂ : AffineSubspace ℝ P} [inst_4 : Nonempty ↥S₁] {ps : Set ↥S₁}   [S₁.directi
on.HasOrthogonalProjection] [S₂.direction.HasOrthogonalProjection] (hS : S₁ ≤ S₂
),   EuclideanGeometry.Cospherical (⇑(AffineSubspace.inclusion hS) '' ps) ↔ Eucl
ideanGeometry.Cospherical ps
参数：hS : S₁ ≤ S₂；⇑(AffineSubspace.inclusion hS) '' ps。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `EuclideanGeometry.Cospherical.subtype_val_iff`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set of points is cospherical in an affine subspace `S₁` if and only if its ima
ge under the
inclusion into a larger affine subspace `S₂` is cospherical.
-/
theorem Cospherical.inclusion_iff {S₁ S₂ : AffineSubspace ℝ P} [Nonempty S₁] {ps : Set S₁}
    [S₁.direction.HasOrthogonalProjection] [S₂.direction.HasOrthogonalProjection] (hS : S₁ ≤ S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) ↔ Cospherical ps := by
  have : Nonempty S₂ := by obtain ⟨p⟩ := ‹Nonempty S₁›; exact ⟨⟨p, hS p.property⟩⟩
  simp [(Cospherical.subtype_val_iff (S := S₂) (ps := AffineSubspace.inclusion hS '' ps)).symm,
    Set.image_image]

/-- Any three points in a cospherical set are affinely independent. -/
/-
**EuclideanGeometry.Cospherical.affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : Set P},   EuclideanGeometry.Cospherical s → ∀ {p : Fin 3 → P}, Set.range p ⊆
 s → Function.Injective p → AffineIndependent ℝ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_not_collinear`：affineIndependent_iff_not_collinear
 {p : Fin 3 -> P} : AffineIndependent k p ↔ ¬Collinear k (Set.range p)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `collinear_iff_of_mem`：collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ 
in s) : Collinear k s ↔ exists v : V, forall p in s, exists r : k, p = r • v +ᵥ 
p₀
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {x y : α} {z : β}, f y = z → (f x ≠ z ↔ x ≠ y)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `EuclideanGeometry.dist_smul_vadd_eq_dist`：dist_smul_vadd_eq_dist {v : V}
 (p₁ p₂ : P) (hv : v != 0) (r : Real) : dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r =
 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / …
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Any three points in a cospherical set are affinely independent.
-/
theorem Cospherical.affineIndependent {s : Set P} (hs : Cospherical s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p := by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_mem_range] at hv
  have hv0 : v ≠ 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : Fin 3) ≠ 0) (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : ∀ i, dist (f i • v +ᵥ p 0) c = r := by
    intro i
    rw [← hf]
    exact hs' i
  have hf0 : f 0 = 0 := by
    have hf0' := hf 0
    rw [eq_comm, ← @vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0'
    simpa [hv0] using hf0'
  have hfi : Function.Injective f := by
    intro i j h
    have hi := hf i
    rw [h, ← hf j] at hi
    exact hpi hi
  simp_rw [← hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := fun i => (hfi.ne_iff' hf0).2
  have hfn0' : ∀ i, i ≠ 0 → f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ := by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by rw [hfn0' 1 (by decide), hfn0' 2 (by decide)]
  exact (by decide : (1 : Fin 3) ≠ 2) (hfi hf12)

/-- Any three points in a cospherical set are affinely independent. -/
/-
**EuclideanGeometry.Cospherical.affineIndependent_of_mem_of_ne** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : Set P},   EuclideanGeometry.Cospherical s →     ∀ {p₁ p₂ p₃ : P}, p₁ ∈ s → p
₂ ∈ s → p₃ ∈ s → p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → AffineIndependent ℝ ![p₁, p₂, p₃]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Cospherical.affineIndependent`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matrix.Fin.cons_vecEmpty`：∀ {α : Type u_1} (x : α), Fin.cons x ![] = ![x
]
· 使用定理 `Matrix.Fin.cons_vecCons`：∀ {n : ℕ} {α : Type u_1} (x y : α) (p : Fin n →
 α),   Fin.cons x (Matrix.vecCons y p) = Matrix.vecCons x (Matrix.vecCons y p)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Any three points in a cospherical set are affinely independent.
-/
theorem Cospherical.affineIndependent_of_mem_of_ne {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (h₃ : p₃ ∈ s) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₁, p₂, p₃] := by
  refine hs.affineIndependent ?_ ?_
  · simp [h₁, h₂, h₃, Set.insert_subset_iff]
  · simp only [Matrix.vecCons, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective, eq_iff_true_of_subsingleton]

/-- The three points of a cospherical set are affinely independent. -/
/-
**EuclideanGeometry.Cospherical.affineIndependent_of_ne** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ p₃ : P},   EuclideanGeometry.Cospherical {p₁, p₂, p₃} → p₁ ≠ p₂ → p₁ ≠ p₃ 
→ p₂ ≠ p₃ → AffineIndependent ℝ ![p₁, p₂, p₃]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Cospherical.affineIndependent_of_mem_of_ne`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
The three points of a cospherical set are affinely independent.
-/
theorem Cospherical.affineIndependent_of_ne {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) : AffineIndependent ℝ ![p₁, p₂, p₃] :=
  hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃

/-- Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`. Then the vector between the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres. (In two dimensions, this says that
the diagonals of a kite are orthogonal.) -/
/-
**EuclideanGeometry.inner_vsub_vsub_of_mem_sphere_of_mem_sphere** 是 Mathlib 中的一个
定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P}
 (hp₁s₁ : p₁ in s₁) (hp₂s₁ : p₂ in s₁) (hp₁s₂ : p₁ in s₂) (hp₂s₂ : p₂ in s₂) : ⟪
s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0
参数：hp₁s₁ : p₁ in s₁；hp₂s₁ : p₂ in s₁；hp₁s₂ : p₁ in s₂；hp₂s₂ : p₂ in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq`：inner_vsub_vsub
_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁) (hc₂ : 
dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p…
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere`：dist_center_
eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ : p
₂ in s) : dist p₁ s.center = dist p₂ s.center

--- 原说明 ---
Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`. Then the vector between
 the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version 
of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres. (In two dimensions,
 this says that
the diagonals of a kite are orthogonal.)
-/
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ ∈ s₁)
    (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) :
    ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

/-- The vector from the midpoint of a chord to the center of the sphere is
orthogonal to the chord. -/
/-
**EuclideanGeometry.Sphere.inner_vsub_center_midpoint_vsub** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P} {s : EuclideanGeometry.Sphere P},   p₁ ∈ s → p₂ ∈ s → inner ℝ (s.cent
er -ᵥ midpoint ℝ p₁ p₂) (p₂ -ᵥ p₁) = 0
参数：s.center -ᵥ midpoint ℝ p₁ p₂；p₂ -ᵥ p₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq`：inner_vsub_vsub
_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁) (hc₂ : 
dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `dist_left_midpoint_eq_dist_right_midpoint`：dist_left_midpoint_eq_dist_ri
ght_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p
₂)
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere`：dist_center_
eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ : p
₂ in s) : dist p₁ s.center = dist p₂ s.center

--- 原说明 ---
The vector from the midpoint of a chord to the center of the sphere is
orthogonal to the chord.
-/
theorem Sphere.inner_vsub_center_midpoint_vsub {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    ⟪s.center -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq
    (dist_left_midpoint_eq_dist_right_midpoint p₁ p₂)
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)

set_option backward.isDefEq.respectTransparency false in
/-- The distance from the center of a sphere to any point strictly between
two points on the sphere is strictly less than the radius. -/
/-
**EuclideanGeometry.Sphere.dist_center_lt_radius_of_sbtw** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ p : P} {s : EuclideanGeometry.Sphere P},   p₁ ∈ s → p₂ ∈ s → Sbtw ℝ p₁ p p
₂ → dist s.center p < s.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `EuclideanGeometry.norm_vsub_center_eq_radius`：norm_vsub_center_eq_radius
 {s : Sphere P} {p : P} (hp : p in s) : ‖p -ᵥ s.center‖ = s.radius
· 使用定理 `vsub_left_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T
 : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p → p₁ = p₂
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `AffineMap.const_apply`：const_apply (p : P2) (q : P1) : (const k P1 p) q 
= p
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
The distance from the center of a sphere to any point strictly between
two points on the sphere is strictly less than the radius.
-/
theorem Sphere.dist_center_lt_radius_of_sbtw {p₁ p₂ p : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp : Sbtw ℝ p₁ p p₂) :
    dist s.center p < s.radius := by
  set o := s.center
  obtain ⟨⟨t, ⟨ht₀, ht₁⟩, hpt⟩, hne₁, hne₂⟩ := hp
  have ht₀' : 0 < t := lt_of_le_of_ne ht₀ fun h => hne₁ <| by
    rw [← hpt, ← h, AffineMap.lineMap_apply_zero]
  have ht₁' : t < 1 := lt_of_le_of_ne ht₁ fun h => hne₂ <| by
    rw [← hpt, h, AffineMap.lineMap_apply_one]
  set u := p₁ -ᵥ o; set v := p₂ -ᵥ o
  have hu : ‖u‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hv : ‖v‖ = s.radius := norm_vsub_center_eq_radius hp₂
  have huv : u ≠ v := fun h => hne₁ <| by
    rw [← hpt, vsub_left_cancel h, AffineMap.lineMap_same, AffineMap.const_apply]
  have hpo : p -ᵥ o = (1 - t) • u + t • v := by
    rw [show p = (AffineMap.lineMap p₁ p₂) t from hpt.symm, AffineMap.lineMap_apply,
      vadd_vsub_assoc, show (p₂ -ᵥ p₁ : V) = v - u from
      (vsub_sub_vsub_cancel_right p₂ p₁ o).symm]
    module
  rw [dist_comm, dist_eq_norm_vsub, hpo]
  have hmem := (strictConvex_closedBall ℝ (0 : V) s.radius)
    (by simp [Metric.mem_closedBall, hu]) (by simp [Metric.mem_closedBall, hv])
    huv (sub_pos.mpr ht₁') ht₀' (sub_add_cancel 1 t)
  rwa [interior_closedBall _ (fun h : s.radius = 0 => huv <|
      (norm_eq_zero.mp (hu.trans h)).trans (norm_eq_zero.mp (hv.trans h)).symm),
    Metric.mem_ball, dist_zero_right] at hmem

/-- The distance from the center of a sphere to the midpoint of a chord
with distinct endpoints is strictly less than the radius. -/
/-
**EuclideanGeometry.Sphere.dist_center_midpoint_lt_radius** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P} {s : EuclideanGeometry.Sphere P},   p₁ ∈ s → p₂ ∈ s → p₁ ≠ p₂ → dist 
s.center (midpoint ℝ p₁ p₂) < s.radius
参数：midpoint ℝ p₁ p₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.dist_center_lt_radius_of_sbtw`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sbtw_midpoint_of_ne`：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R
 x (midpoint R x y) y

--- 原说明 ---
The distance from the center of a sphere to the midpoint of a chord
with distinct endpoints is strictly less than the radius.
-/
theorem Sphere.dist_center_midpoint_lt_radius {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
    dist s.center (midpoint ℝ p₁ p₂) < s.radius :=
  s.dist_center_lt_radius_of_sbtw hp₁ hp₂ (sbtw_midpoint_of_ne ℝ hp₁p₂)

/-- Two spheres intersect in at most two points in a two-dimensional subspace containing their
centers; this is a version of `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` for bundled
spheres. -/
/-
**EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two** 是 
Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : AffineSubspac
e Real P} [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = 
2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs₁ : s₁.center in s) (hs₂ : s₂.center in s
) (hp₁s : p₁ in s) (hp₂s : p₂ in s) (hps : p in s) (hs : s₁ != s₂) (hp : p₁ != p
₂) (hp₁s₁ : p₁ in s₁) (hp₂s₁ : p₂ in s₁) (hps₁ : p in s₁) (hp₁s₂ : p₁ in s₂) (hp
₂s₂ : p₂ in s₂) (hps₂ : p in s₂) : p = p₁ ∨ p = p₂
参数：hd : finrank Real s.direction = 2；hs₁ : s₁.center in s；hs₂ : s₂.center in s；h
p₁s : p₁ in s；hp₂s : p₂ in s；hps : p in s；hs : s₁ != s₂；hp : p₁ != p₂；hp₁s₁ : p₁
 in s₁；hp₂s₁ : p₂ in s₁；hps₁ : p in s₁；hp₁s₂ : p₁ in s₂；hp₂s₂ : p₂ in s₂；hps₂ : 
p in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two`：eq_
of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : AffineSubspace Real P} [Fini
teDimensional Real s.direction] (hd : finrank Real s.dire…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.center_ne_iff_ne_of_mem`：∀ {P : Type u_2} [inst
 : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   p ∈ s₁ → p ∈ s
₂ → (s₁.center ≠ s₂.center ↔ s₁ ≠ s₂)

--- 原说明 ---
Two spheres intersect in at most two points in a two-dimensional subspace contai
ning their
centers; this is a version of `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
` for bundled
spheres.
-/
theorem eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {s₁ s₂ : Sphere P}
    {p₁ p₂ p : P} (hs₁ : s₁.center ∈ s) (hs₂ : s₂.center ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
    (hps : p ∈ s) (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂) (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁)
    (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Two spheres intersect in at most two points in two-dimensional space; this is a version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres. -/
/-
**EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional Real V
] (hd : finrank Real V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ != s₂) (hp
 : p₁ != p₂) (hp₁s₁ : p₁ in s₁) (hp₂s₁ : p₂ in s₁) (hps₁ : p in s₁) (hp₁s₂ : p₁ 
in s₂) (hp₂s₂ : p₂ in s₂) (hps₂ : p in s₂) : p = p₁ ∨ p = p₂
参数：hd : finrank Real V = 2；hs : s₁ != s₂；hp : p₁ != p₂；hp₁s₁ : p₁ in s₁；hp₂s₁ : 
p₂ in s₁；hps₁ : p in s₁；hp₁s₂ : p₁ in s₂；hp₂s₂ : p₂ in s₂；hps₂ : p in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`：eq_of_dist
_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional Real V] (hd : finrank Real V
 = 2) {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : Real} (hc : c₁ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.center_ne_iff_ne_of_mem`：∀ {P : Type u_2} [inst
 : MetricSpace P] {s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   p ∈ s₁ → p ∈ s
₂ → (s₁.center ≠ s₂.center ↔ s₁ ≠ s₂)

--- 原说明 ---
Two spheres intersect in at most two points in two-dimensional space; this is a 
version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres.
-/
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂)
    (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
    (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is positive unless the points are equal. -/
/-
**EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：inner_pos_or_eq_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in 
s) (hp₂ : dist p₂ s.center <= s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = 
p₂
参数：hp₁ : p₁ in s；hp₂ : dist p₂ s.center <= s.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `real_inner_le_norm`：real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * 
‖y‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Given a point on a sphere and a point not outside it, the inner product between 
the
difference of those points and the radius vector is positive unless the points a
re equal.
-/
theorem inner_pos_or_eq_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = p₂ := by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine Or.inl ?_
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center, inner_sub_left,
    real_inner_self_eq_norm_mul_norm, sub_pos]
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) ?_
  · rwa [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hp₁]
  · rcases hp₂.lt_or_eq with (hp₂' | hp₂')
    · refine ((real_inner_le_norm _ _).trans_lt (mul_lt_mul_of_pos_right ?_ ?_)).ne
      · rwa [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      · rw [norm_pos_iff, vsub_ne_zero]
        rintro rfl
        rw [← hp₁] at hp₂'
        refine (dist_nonneg.not_gt : ¬dist p₂ s.center < 0) ?_
        simpa using hp₂'
    · rw [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      nth_rw 1 [← hp₂']
      rw [Ne, inner_eq_norm_mul_iff_real, hp₂', ← sub_eq_zero, ← smul_sub,
        vsub_sub_vsub_cancel_right, ← Ne, smul_ne_zero_iff, vsub_ne_zero,
        and_iff_left (Ne.symm h), norm_ne_zero_iff, vsub_ne_zero]
      rintro rfl
      refine h (Eq.symm ?_)
      simpa using hp₂'

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is nonnegative. -/
/-
**EuclideanGeometry.inner_nonneg_of_dist_le_radius** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：inner_nonneg_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) 
(hp₂ : dist p₂ s.center <= s.radius) : 0 <= ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫
参数：hp₁ : p₁ in s；hp₂ : dist p₂ s.center <= s.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius`：inner_pos_or_eq_of_
dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : dist p₂ s.cente
r <= s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.c…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0

--- 原说明 ---
Given a point on a sphere and a point not outside it, the inner product between 
the
difference of those points and the radius vector is nonnegative.
-/
theorem inner_nonneg_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 ≤ ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp

/-- Given a point on a sphere and a point inside it, the inner product between the difference of
those points and the radius vector is positive. -/
/-
**EuclideanGeometry.inner_pos_of_dist_lt_radius** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：inner_pos_of_dist_lt_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp
₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫
参数：hp₁ : p₁ in s；hp₂ : dist p₂ s.center < s.radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius`：inner_pos_or_eq_of_
dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : dist p₂ s.cente
r <= s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.c…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Given a point on a sphere and a point inside it, the inner product between the d
ifference of
those points and the radius vector is positive.
-/
theorem inner_pos_of_dist_lt_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h

/-- Given two distinct points on a sphere, the inner product of the chord with
the radius vector at one endpoint is negative. -/
/-
**EuclideanGeometry.inner_vsub_center_vsub_pos** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：inner_vsub_center_vsub_pos {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂
 : p₂ in s) (hp₁p₂ : p₁ != p₂) : 0 < ⟪p₂ -ᵥ p₁, s.center -ᵥ p₁⟫
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₁p₂ : p₁ != p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.norm_vsub_center_eq_radius`：norm_vsub_center_eq_radius
 {s : Sphere P} {p : P} (hp : p in s) : ‖p -ᵥ s.center‖ = s.radius
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `norm_add_sq_real`：norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2
 * ⟪x, y⟫_Real + ‖y‖ ^ 2
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
Given two distinct points on a sphere, the inner product of the chord with
the radius vector at one endpoint is negative.
-/
theorem inner_vsub_center_vsub_pos {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
    0 < ⟪p₂ -ᵥ p₁, s.center -ᵥ p₁⟫ := by
  have hp₁' : ‖p₁ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hp₂' : ‖p₂ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₂
  have hd : ‖p₂ -ᵥ s.center‖ ^ 2 =
      ‖p₂ -ᵥ p₁‖ ^ 2 + 2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ s.center⟫ + ‖p₁ -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_cancel p₂ p₁ s.center, norm_add_sq_real]
  rw [hp₂', hp₁', ← neg_vsub_eq_vsub_rev s.center p₁, inner_neg_right] at hd
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hp₁p₂.symm))]

/-- Given three collinear points, two on a sphere and one not outside it, the one not outside it
is weakly between the other two points. -/
/-
**EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：wbtw_of_collinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P} (
h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : dist p₂ s.cent
er <= s.radius) (hp₃ : p₃ in s) (hp₁p₃ : p₁ != p₃) : Wbtw Real p₁ p₂ p₃
参数：h : Collinear Real ({p₁, p₂, p₃} : Set P)；hp₁ : p₁ in s；hp₂ : dist p₂ s.cente
r <= s.radius；hp₃ : p₃ in s；hp₁p₃ : p₁ != p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.wbtw_of_dist_eq_of_dist_le`：Collinear.wbtw_of_dist_eq_of_dist_
le {p p₁ p₂ p₃ : P} {r : Real} (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ 
: dist p₁ p = r) (hp₂ : di…
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F

--- 原说明 ---
Given three collinear points, two on a sphere and one not outside it, the one no
t outside it
is weakly between the other two points.
-/
theorem wbtw_of_collinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center ≤ s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ :=
  h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

/-- Given three collinear points, two on a sphere and one inside it, the one inside it is
strictly between the other two points. -/
/-
**EuclideanGeometry.sbtw_of_collinear_of_dist_center_lt_radius** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：sbtw_of_collinear_of_dist_center_lt_radius {s : Sphere P} {p₁ p₂ p₃ : P} (
h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : dist p₂ s.cent
er < s.radius) (hp₃ : p₃ in s) (hp₁p₃ : p₁ != p₃) : Sbtw Real p₁ p₂ p₃
参数：h : Collinear Real ({p₁, p₂, p₃} : Set P)；hp₁ : p₁ in s；hp₂ : dist p₂ s.cente
r < s.radius；hp₃ : p₃ in s；hp₁p₃ : p₁ != p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.sbtw_of_dist_eq_of_dist_lt`：Collinear.sbtw_of_dist_eq_of_dist_
lt {p p₁ p₂ p₃ : P} {r : Real} (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ 
: dist p₁ p = r) (hp₂ : di…
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F

--- 原说明 ---
Given three collinear points, two on a sphere and one inside it, the one inside 
it is
strictly between the other two points.
-/
theorem sbtw_of_collinear_of_dist_center_lt_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center < s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ :=
  h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

namespace Sphere

variable {s : Sphere P} {p₁ p₂ : P}

/-
**EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_dist** 是 Mathlib 中的一个引
理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_mem_and_mem_and_dist : s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in
 s ∧ dist p₁ p₂ = 2 * s.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.right_mem`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.dist_left_right`：∀ {V : Type u_1} {P
 : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
· 使用定理 `AffineEquiv.pointReflection_apply`：pointReflection_apply (x y : P₁) : po
intReflection k x y = (x -ᵥ y) +ᵥ x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `eq_of_norm_eq_of_norm_add_eq`：eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖
y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma isDiameter_iff_mem_and_mem_and_dist :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ p₂ ∈ s ∧ dist p₁ p₂ = 2 * s.radius := by
  refine ⟨fun h ↦ ⟨h.left_mem, h.right_mem, h.dist_left_right⟩, fun ⟨h₁, h₂, hr⟩ ↦ ⟨h₁, ?_⟩⟩
  rw [midpoint_eq_iff, AffineEquiv.pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq]
  apply eq_of_norm_eq_of_norm_add_eq
  · simp_rw [← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
  · simp_rw [vsub_add_vsub_cancel, ← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
    rw [dist_comm, hr, two_mul]
/-
**EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_wbtw** 是 Mathlib 中的一个引
理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_iff_mem_and_mem_and_wbtw : s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in
 s ∧ Wbtw Real p₁ s.center p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.left_mem`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.right_mem`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAddTorso…
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.wbtw`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAddTorso…
· 使用定理 `Wbtw.dist_add_dist`：Wbtw.dist_add_dist {x y z : P} (h : Wbtw Real x y z)
 : dist x y + dist y z = dist x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_dist`：isDiameter
_iff_mem_and_mem_and_dist : s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in s ∧ dist p₁ p₂ 
= 2 * s.radius
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
-/
lemma isDiameter_iff_mem_and_mem_and_wbtw :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ p₂ ∈ s ∧ Wbtw ℝ p₁ s.center p₂ := by
  refine ⟨fun h ↦ ⟨h.left_mem, h.right_mem, h.wbtw⟩, fun ⟨h₁, h₂, hr⟩ ↦ ?_⟩
  have hd := hr.dist_add_dist
  rw [mem_sphere.1 h₁, mem_sphere'.1 h₂, ← two_mul, eq_comm] at hd
  exact isDiameter_iff_mem_and_mem_and_dist.2 ⟨h₁, h₂, hd⟩

/-- The center lies on the line through two points of a sphere if and only if those
points are the endpoints of a diameter. -/
/-
**EuclideanGeometry.Sphere.center_mem_affineSpan_pair_iff_isDiameter** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：center_mem_affineSpan_pair_iff_isDiameter (hp₁ : p₁ in s) (hp₂ : p₂ in s) 
: s.center in line[Real, p₁, p₂] ↔ s.IsDiameter p₁ p₂
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_wbtw`：isDiameter
_iff_mem_and_mem_and_wbtw : s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in s ∧ Wbtw Real p
₁ s.center p₂
· 使用定理 `EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius`：wbtw_of_co
llinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P} (h : Collinear Re
al ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : …
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `collinear_insert_of_mem_affineSpan_pair`：collinear_insert_of_mem_affineS
pan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) : Collinear k ({p₁, p₂, p₃} 
: Set P)
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `Wbtw.mem_affineSpan`：Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) 
: y in line[R, x, z]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The center lies on the line through two points of a sphere if and only if those
points are the endpoints of a diameter.
-/
theorem center_mem_affineSpan_pair_iff_isDiameter (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    s.center ∈ line[ℝ, p₁, p₂] ↔ s.IsDiameter p₁ p₂ := by
  rcases eq_or_ne p₁ p₂ with rfl | hp₁p₂
  · simp [isDiameter_iff_left_mem_and_midpoint_eq_center, hp₁, eq_comm]
  · rw [isDiameter_iff_mem_and_mem_and_wbtw]
    refine ⟨fun h => ⟨hp₁, hp₂, ?_⟩, fun h => h.2.2.mem_affineSpan⟩
    refine wbtw_of_collinear_of_dist_center_le_radius ?_ hp₁ ?_ hp₂ hp₁p₂
    · rw [Set.insert_comm]; exact collinear_insert_of_mem_affineSpan_pair h
    · simpa using radius_nonneg_of_mem hp₁

end Sphere

end EuclideanSpace

end EuclideanGeometry

