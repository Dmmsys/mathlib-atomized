/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.LinearMap.Prod
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Module

/-!
# Star-convex sets

This file defines star-convex sets (aka star domains, star-shaped set, radially convex set).

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Main declarations

* `StarConvex 𝕜 x s`: `s` is star-convex at `x` with scalars `𝕜`.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.

## TODO

The closure of a star-convex set is star-convex.

A nonempty open star-convex set in `ℝ^n` is diffeomorphic to the entire space.

Replace with `Convexity.IsStarConvexSet`.
-/

@[expose] public section


open Set

open Convex Pointwise

variable {𝕜 E F : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (x : E) (s : Set E)

/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
/-
**StarConvex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommM
onoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop
参数：𝕜 : Type*；x : E；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a
 point in `s` is
contained in `s`.
-/
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

variable {𝕜 x s} {t : Set E}
/-
**starConvex_iff_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_segment_subset : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> [
x -[𝕜] y] subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starConvex_iff_segment_subset : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s := by
  constructor
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    exact h hy ha hb hab
  · rintro h y hy a b ha hb hab
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩
/-
**StarConvex.segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.segment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y in s) : [
x -[𝕜] y] subseteq s
参数：h : StarConvex 𝕜 x s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `starConvex_iff_segment_subset`：starConvex_iff_segment_subset : StarConve
x 𝕜 x s ↔ forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
-/
theorem StarConvex.segment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
  starConvex_iff_segment_subset.1 h hy
/-
**StarConvex.openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.openSegment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y in s)
 : openSegment 𝕜 x y subseteq s
参数：h : StarConvex 𝕜 x s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `StarConvex.segment_subset`：StarConvex.segment_subset (h : StarConvex 𝕜 x
 s) {y : E} (hy : y in s) : [x -[𝕜] y] subseteq s
-/
theorem StarConvex.openSegment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

/-- Alternative definition of star-convexity, in terms of pointwise set operations. -/
/-
**starConvex_iff_pointwise_add_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_pointwise_add_subset : StarConvex 𝕜 x s ↔ forall ⦃a b : 𝕜⦄,
 0 <= a -> 0 <= b -> a + b = 1 -> a • {x} + b • s subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
Alternative definition of star-convexity, in terms of pointwise set operations.
-/
theorem starConvex_iff_pointwise_add_subset :
    StarConvex 𝕜 x s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • {x} + b • s ⊆ s := by
  refine
    ⟨?_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, ⟨u, rfl : u = x, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  exact hA hv ha hb hab
/-
**starConvex_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_empty (x : E) : StarConvex 𝕜 x ∅
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starConvex_empty (x : E) : StarConvex 𝕜 x ∅ := fun _ hy => hy.elim
/-
**starConvex_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_univ (x : E) : StarConvex 𝕜 x univ
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem starConvex_univ (x : E) : StarConvex 𝕜 x univ := fun _ _ _ _ _ _ _ => trivial
/-
**StarConvex.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarCon
vex 𝕜 x (s inter t)
参数：hs : StarConvex 𝕜 x s；ht : StarConvex 𝕜 x t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarConvex 𝕜 x (s ∩ t) :=
  fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩
/-
**starConvex_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_sInter {S : Set (Set E)} (h : forall s in S, StarConvex 𝕜 x s) 
: StarConvex 𝕜 x (⋂₀ S)
参数：Set E；h : forall s in S, StarConvex 𝕜 x s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starConvex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋂₀ S) := fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab
/-
**starConvex_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, StarConvex 𝕜
 x (s i)) : StarConvex 𝕜 x (⋂ i, s i)
参数：h : forall i, StarConvex 𝕜 x (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_sInter`：starConvex_sInter {S : Set (Set E)} (h : forall s in 
S, StarConvex 𝕜 x s) : StarConvex 𝕜 x (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem starConvex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋂ i, s i) :=
  sInter_range s ▸ starConvex_sInter <| forall_mem_range.2 h
/-
**starConvex_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, StarConvex 𝕜
 x (s i)) : StarConvex 𝕜 x (⋂ i, s i)
参数：h : forall i, StarConvex 𝕜 x (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_sInter`：starConvex_sInter {S : Set (Set E)} (h : forall s in 
S, StarConvex 𝕜 x s) : StarConvex 𝕜 x (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem starConvex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋂ (i) (j), s i j) :=
  starConvex_iInter fun i => starConvex_iInter (h i)
/-
**StarConvex.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.union (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarCon
vex 𝕜 x (s union t)
参数：hs : StarConvex 𝕜 x s；ht : StarConvex 𝕜 x t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StarConvex.union (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) :
    StarConvex 𝕜 x (s ∪ t) := by
  rintro y (hy | hy) a b ha hb hab
  · exact Or.inl (hs hy ha hb hab)
  · exact Or.inr (ht hy ha hb hab)
/-
**starConvex_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hs : forall i, StarConvex 
𝕜 x (s i)) : StarConvex 𝕜 x (⋃ i, s i)
参数：hs : forall i, StarConvex 𝕜 x (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem starConvex_iUnion {ι : Sort*} {s : ι → Set E} (hs : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋃ i, s i) := by
  rintro y hy a b ha hb hab
  rw [mem_iUnion] at hy ⊢
  obtain ⟨i, hy⟩ := hy
  exact ⟨i, hs i hy ha hb hab⟩
/-
**starConvex_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hs : forall i, StarConvex 
𝕜 x (s i)) : StarConvex 𝕜 x (⋃ i, s i)
参数：hs : forall i, StarConvex 𝕜 x (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem starConvex_iUnion₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋃ (i) (j), s i j) :=
  starConvex_iUnion fun i => starConvex_iUnion (h i)
/-
**starConvex_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_sUnion {S : Set (Set E)} (hS : forall s in S, StarConvex 𝕜 x s)
 : StarConvex 𝕜 x (⋃₀ S)
参数：Set E；hS : forall s in S, StarConvex 𝕜 x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `starConvex_iUnion`：starConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hs : 
forall i, StarConvex 𝕜 x (s i)) : StarConvex 𝕜 x (⋃ i, s i)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem starConvex_sUnion {S : Set (Set E)} (hS : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact starConvex_iUnion fun s => hS _ s.2
/-
**StarConvex.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s) (h
t : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t)
参数：hs : StarConvex 𝕜 x s；ht : StarConvex 𝕜 y t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s)
    (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t) := fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩
/-
**starConvex_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)]
 [forall i, SMul 𝕜 (E i)] {x : forall i, E i} {s : Set ι} {t : forall i, Set (E 
i)} (ht : forall ⦃i⦄, i in s -> StarConvex 𝕜 (x i) (t i)) : StarConvex 𝕜 x (s.pi
 t)
参数：E i；E i；E i；ht : forall ⦃i⦄, i in s -> StarConvex 𝕜 (x i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starConvex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {x : ∀ i, E i} {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → StarConvex 𝕜 (x i) (t i)) :
    StarConvex 𝕜 x (s.pi t) := fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {x y z : E} {s : Set E}

/-
**StarConvex.mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.mem [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s) (h : s.Nonempty)
 : x in s
参数：hs : StarConvex 𝕜 x s；h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem StarConvex.mem [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s) (h : s.Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := h
  convert! hs hy zero_le_one le_rfl (add_zero 1)
  rw [one_smul, zero_smul, add_zero]
/-
**starConvex_iff_forall_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_forall_pos (hx : x in s) : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y
 in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem starConvex_iff_forall_pos (hx : x ∈ s) : StarConvex 𝕜 x s ↔
    ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, one_smul, zero_smul, zero_add]
  obtain rfl | hb := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, one_smul, zero_smul, add_zero]
  exact h hy ha hb hab
/-
**starConvex_iff_forall_ne_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_forall_ne_pos (hx : x in s) : StarConvex 𝕜 x s ↔ forall ⦃y⦄
, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b
 • y in s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem starConvex_iff_forall_ne_pos (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔
      ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, zero_smul, one_smul, zero_add]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, zero_smul, one_smul, add_zero]
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  exact h hy hxy ha' hb' hab
/-
**starConvex_iff_openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_openSegment_subset [ZeroLEOneClass 𝕜] (hx : x in s) : StarC
onvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> openSegment 𝕜 x y subseteq s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `starConvex_iff_segment_subset`：starConvex_iff_segment_subset : StarConve
x 𝕜 x s ↔ forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `openSegment_subset_iff_segment_subset`：openSegment_subset_iff_segment_su
bset (hx : x in s) (hy : y in s) : openSegment 𝕜 x y subseteq s ↔ [x -[𝕜] y] sub
seteq s
-/
theorem starConvex_iff_openSegment_subset [ZeroLEOneClass 𝕜] (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  starConvex_iff_segment_subset.trans <|
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm
/-
**starConvex_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_singleton (x : E) : StarConvex 𝕜 x {x}
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem starConvex_singleton (x : E) : StarConvex 𝕜 x {x} := by
  rintro y (rfl : y = x) a b _ _ hab
  exact Convex.combo_self hab _
/-
**StarConvex.linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.linear_image (hs : StarConvex 𝕜 x s) (f : E ->ₗ[𝕜] F) : StarCon
vex 𝕜 (f x) (f '' s)
参数：hs : StarConvex 𝕜 x s；f : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem StarConvex.linear_image (hs : StarConvex 𝕜 x s) (f : E →ₗ[𝕜] F) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩
/-
**StarConvex.is_linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.is_linear_image (hs : StarConvex 𝕜 x s) {f : E -> F} (hf : IsLi
nearMap 𝕜 f) : StarConvex 𝕜 (f x) (f '' s)
参数：hs : StarConvex 𝕜 x s；hf : IsLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.linear_image`：StarConvex.linear_image (hs : StarConvex 𝕜 x s)
 (f : E ->ₗ[𝕜] F) : StarConvex 𝕜 (f x) (f '' s)
-/
theorem StarConvex.is_linear_image (hs : StarConvex 𝕜 x s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    StarConvex 𝕜 (f x) (f '' s) :=
  hs.linear_image <| hf.mk' f
/-
**StarConvex.linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.linear_preimage {s : Set F} (f : E ->ₗ[𝕜] F) (hs : StarConvex 𝕜
 (f x) s) : StarConvex 𝕜 x (f ⁻¹' s)
参数：f : E ->ₗ[𝕜] F；hs : StarConvex 𝕜 (f x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem StarConvex.linear_preimage {s : Set F} (f : E →ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hy ha hb hab
/-
**StarConvex.is_linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.is_linear_preimage {s : Set F} {f : E -> F} (hs : StarConvex 𝕜 
(f x) s) (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 x (preimage f s)
参数：hs : StarConvex 𝕜 (f x) s；hf : IsLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.linear_preimage`：StarConvex.linear_preimage {s : Set F} (f : 
E ->ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) : StarConvex 𝕜 x (f ⁻¹' s)
-/
theorem StarConvex.is_linear_preimage {s : Set F} {f : E → F} (hs : StarConvex 𝕜 (f x) s)
    (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 x (preimage f s) :=
  hs.linear_preimage <| hf.mk' f
/-
**StarConvex.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t)
 : StarConvex 𝕜 (x + y) (s + t)
参数：hs : StarConvex 𝕜 x s；ht : StarConvex 𝕜 y t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.add_image_prod`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, (fun 
x => x.1 + x.2) '' s ×ˢ t = s + t
· 使用定理 `StarConvex.is_linear_image`：StarConvex.is_linear_image (hs : StarConvex 
𝕜 x s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 (f x) (f '' s)
· 使用定理 `StarConvex.prod`：StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : S
tarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t)
· 使用定理 `IsLinearMap.isLinearMap_add`：isLinearMap_add [AddCommMonoid M] [Module R
 M] : IsLinearMap R fun x : M × M => x.1 + x.2
-/
theorem StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x + y) (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add
/-
**StarConvex.add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E) : StarConvex 𝕜 (z + x)
 ((fun x => z + x) '' s)
参数：hs : StarConvex 𝕜 x s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (z + x) ((fun x => z + x) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]
/-
**StarConvex.add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.add_right (hs : StarConvex 𝕜 x s) (z : E) : StarConvex 𝕜 (x + z
) ((fun x => x + z) '' s)
参数：hs : StarConvex 𝕜 x s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem StarConvex.add_right (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (x + z) ((fun x => x + z) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

/-- The translation of a star-convex set is also star-convex. -/
/-
**StarConvex.preimage_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.preimage_add_right (hs : StarConvex 𝕜 (z + x) s) : StarConvex 𝕜
 x ((fun x => z + x) ⁻¹' s)
参数：hs : StarConvex 𝕜 (z + x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂

--- 原说明 ---
The translation of a star-convex set is also star-convex.
-/
theorem StarConvex.preimage_add_right (hs : StarConvex 𝕜 (z + x) s) :
    StarConvex 𝕜 x ((fun x => z + x) ⁻¹' s) := by
  intro y hy a b ha hb hab
  have h := hs hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/-- The translation of a star-convex set is also star-convex. -/
/-
**StarConvex.preimage_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.preimage_add_left (hs : StarConvex 𝕜 (x + z) s) : StarConvex 𝕜 
x ((fun x => x + z) ⁻¹' s)
参数：hs : StarConvex 𝕜 (x + z) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `StarConvex.preimage_add_right`：StarConvex.preimage_add_right (hs : StarC
onvex 𝕜 (z + x) s) : StarConvex 𝕜 x ((fun x => z + x) ⁻¹' s)

--- 原说明 ---
The translation of a star-convex set is also star-convex.
-/
theorem StarConvex.preimage_add_left (hs : StarConvex 𝕜 (x + z) s) :
    StarConvex 𝕜 x ((fun x => x + z) ⁻¹' s) := by
  rw [add_comm] at hs
  simpa only [add_comm] using hs.preimage_add_right

end Module

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x y : E}

/-
**StarConvex.sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) : StarConve
x 𝕜 (x - y) ((fun x : E × E => x.1 - x.2) '' s)
参数：E × E；hs : StarConvex 𝕜 (x, y) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.is_linear_image`：StarConvex.is_linear_image (hs : StarConvex 
𝕜 x s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 (f x) (f '' s)
· 使用定理 `IsLinearMap.isLinearMap_sub`：isLinearMap_sub [AddCommGroup M] [Module R 
M] : IsLinearMap R fun x : M × M => x.1 - x.2
-/
theorem StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) :
    StarConvex 𝕜 (x - y) ((fun x : E × E => x.1 - x.2) '' s) :=
  hs.is_linear_image IsLinearMap.isLinearMap_sub

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {x : E} {s : Set E}

/-
**StarConvex.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c 
• s)
参数：hs : StarConvex 𝕜 x s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.linear_image`：StarConvex.linear_image (hs : StarConvex 𝕜 x s)
 (f : E ->ₗ[𝕜] F) : StarConvex 𝕜 (f x) (f '' s)
-/
theorem StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c • s) :=
  hs.linear_image <| LinearMap.lsmul _ _ c
/-
**StarConvex.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.zero_smul (hs : StarConvex 𝕜 0 s) (c : 𝕜) : StarConvex 𝕜 0 (c •
 s)
参数：hs : StarConvex 𝕜 0 s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `StarConvex.smul`：StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarC
onvex 𝕜 (c • x) (c • s)
-/
theorem StarConvex.zero_smul (hs : StarConvex 𝕜 0 s) (c : 𝕜) : StarConvex 𝕜 0 (c • s) := by
  simpa using hs.smul c
/-
**StarConvex.preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.preimage_smul {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s) : StarConve
x 𝕜 x ((fun z => c • z) ⁻¹' s)
参数：hs : StarConvex 𝕜 (c • x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.linear_preimage`：StarConvex.linear_preimage {s : Set F} (f : 
E ->ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) : StarConvex 𝕜 x (f ⁻¹' s)
-/
theorem StarConvex.preimage_smul {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s) :
    StarConvex 𝕜 x ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)
/-
**StarConvex.affinity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.affinity (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜) : StarConvex 𝕜
 (z + c • x) ((fun x => z + c • x) '' s)
参数：hs : StarConvex 𝕜 x s；z : E；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.add_left`：StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E)
 : StarConvex 𝕜 (z + x) ((fun x => z + x) '' s)
· 使用定理 `StarConvex.smul`：StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarC
onvex 𝕜 (c • x) (c • s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
-/
theorem StarConvex.affinity (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜) :
    StarConvex 𝕜 (z + c • x) ((fun x => z + c • x) '' s) := by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

end AddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddRightMono 𝕜] [AddCommMonoid E] [SMulWithZero 𝕜 E] {s : Set E}

/-
**starConvex_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_zero_iff : StarConvex 𝕜 0 s ↔ forall ⦃x : E⦄, x in s -> forall 
⦃a : 𝕜⦄, 0 <= a -> a <= 1 -> a • x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
-/
theorem starConvex_zero_iff :
    StarConvex 𝕜 0 s ↔ ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃a : 𝕜⦄, 0 ≤ a → a ≤ 1 → a • x ∈ s := by
  refine
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => ?_, fun h a b ha hb hab => ?_⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    exact h hb (by rw [← hab]; exact le_add_of_nonneg_left ha)

end AddCommMonoid

section AddCommGroup

section AddRightMono

variable [AddRightMono 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  {x y : E} {s t : Set E}

/-
**StarConvex.add_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s) (hy : x + y in s) {t : 𝕜} 
(ht₀ : 0 <= t) (ht₁ : t <= 1) : x + t • y in s
参数：hs : StarConvex 𝕜 x s；hy : x + y in s；ht₀ : 0 <= t；ht₁ : t <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
-/
theorem StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s) (hy : x + y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)
/-
**StarConvex.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht₀ : 0
 <= t) (ht₁ : t <= 1) : t • x in s
参数：hs : StarConvex 𝕜 0 s；hx : x in s；ht₀ : 0 <= t；ht₁ : t <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `StarConvex.add_smul_mem`：StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s)
 (hy : x + y in s) {t : 𝕜} (ht₀ : 0 <= t) (ht₁ : t <= 1) : x + t • y in s
-/
theorem StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : t • x ∈ s := by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁
/-
**StarConvex.add_smul_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.add_smul_sub_mem (hs : StarConvex 𝕜 x s) (hy : y in s) {t : 𝕜} 
(ht₀ : 0 <= t) (ht₁ : t <= 1) : x + t • (y - x) in s
参数：hs : StarConvex 𝕜 x s；hy : y in s；ht₀ : 0 <= t；ht₁ : t <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.segment_subset`：StarConvex.segment_subset (h : StarConvex 𝕜 x
 s) {y : E} (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image'`：segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜
 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem StarConvex.add_smul_sub_mem (hs : StarConvex 𝕜 x s) (hy : y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • (y - x) ∈ s := by
  apply hs.segment_subset hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

end AddRightMono

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {x y : E} {s t : Set E}

/-- The preimage of a star-convex set under an affine map is star-convex. -/
/-
**StarConvex.affine_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜
 (f x) s) : StarConvex 𝕜 x (f ⁻¹' s)
参数：f : E ->ᵃ[𝕜] F；hs : StarConvex 𝕜 (f x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Convex.combo_affine_apply`：Convex.combo_affine_apply {x y : E} {a b : 𝕜}
 {f : E ->ᵃ[𝕜] F} (h : a + b = 1) : f (a • x + b • y) = a • f x + b • f y

--- 原说明 ---
The preimage of a star-convex set under an affine map is star-convex.
-/
theorem StarConvex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hy ha hb hab

/-- The image of a star-convex set under an affine map is star-convex. -/
/-
**StarConvex.affine_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.affine_image (f : E ->ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x 
s) : StarConvex 𝕜 (f x) (f '' s)
参数：f : E ->ᵃ[𝕜] F；hs : StarConvex 𝕜 x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.combo_affine_apply`：Convex.combo_affine_apply {x y : E} {a b : 𝕜}
 {f : E ->ᵃ[𝕜] F} (h : a + b = 1) : f (a • x + b • y) = a • f x + b • f y

--- 原说明 ---
The image of a star-convex set under an affine map is star-convex.
-/
theorem StarConvex.affine_image (f : E →ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x s) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, ?_⟩⟩
  rw [Convex.combo_affine_apply hab, hy'f]
/-
**StarConvex.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-x) (-s)
参数：hs : StarConvex 𝕜 x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `StarConvex.is_linear_image`：StarConvex.is_linear_image (hs : StarConvex 
𝕜 x s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 (f x) (f '' s)
· 使用定理 `IsLinearMap.isLinearMap_neg`：isLinearMap_neg : IsLinearMap R fun z : M =
> -z
-/
theorem StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-x) (-s) := by
  rw [← image_neg_eq_neg]
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg
/-
**StarConvex.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) : StarConve
x 𝕜 (x - y) (s - t)
参数：hs : StarConvex 𝕜 x s；ht : StarConvex 𝕜 y t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `StarConvex.add`：StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht :
 StarConvex 𝕜 y t) : StarConvex 𝕜 (x + y) (s + t)
· 使用定理 `StarConvex.neg`：StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-
x) (-s)
-/
theorem StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x - y) (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroup

section OrderedAddCommGroup

variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [IsStrictOrderedModule 𝕜 E] [PosSMulReflectLT 𝕜 E] {x y : E}

/-- If `x < y`, then `(Set.Iic x)ᶜ` is star convex at `y`. -/
/-
**starConvex_compl_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y (Iic x)ᶜ
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `starConvex_iff_forall_pos`：starConvex_iff_forall_pos (hx : x in s) : Sta
rConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b 
= 1 -> a • x + …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_smul_lt_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : 
α} {b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [
inst_3 : Zero α] [PosSM…
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
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
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `x < y`, then `(Set.Iic x)ᶜ` is star convex at `y`.
-/
lemma starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y (Iic x)ᶜ := by
  refine (starConvex_iff_forall_pos <| by simp [h.not_ge]).mpr fun z hz a b ha hb hab ↦ ?_
  rw [mem_compl_iff, mem_Iic] at hz ⊢
  contrapose hz
  refine (lt_of_smul_lt_smul_of_nonneg_left ?_ hb.le).le
  calc
    b • z ≤ (a + b) • x - a • y := by rwa [le_sub_iff_add_le', hab, one_smul]
    _ < b • x := by
      rw [add_smul, sub_lt_iff_lt_add']
      gcongr

/-- If `x < y`, then `(Set.Ici y)ᶜ` is star convex at `x`. -/
/-
**starConvex_compl_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：starConvex_compl_Ici (h : x < y) : StarConvex 𝕜 x (Ici y)ᶜ
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `starConvex_compl_Iic`：starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y 
(Iic x)ᶜ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…

--- 原说明 ---
If `x < y`, then `(Set.Ici y)ᶜ` is star convex at `x`.
-/
lemma starConvex_compl_Ici (h : x < y) : StarConvex 𝕜 x (Ici y)ᶜ :=
  starConvex_compl_Iic (E := Eᵒᵈ) h

end OrderedAddCommGroup

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x : E} {s : Set E}

/-- Alternative definition of star-convexity, using division. -/
/-
**starConvex_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_div : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> forall ⦃a b 
: 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b)) • x + (b / (a + b)) • y in 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
Alternative definition of star-convexity, using division.
-/
theorem starConvex_iff_div : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s →
    ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
    · positivity
    · rw [← add_div]
      exact div_self hab.ne',
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    rw [hab, div_one, div_one] at h'
    exact h' zero_lt_one⟩
/-
**StarConvex.mem_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarConvex.mem_smul (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht : 1 
<= t) : x in t • s
参数：hs : StarConvex 𝕜 0 s；hx : x in s；ht : 1 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `StarConvex.smul_mem`：StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x
 in s) {t : 𝕜} (ht₀ : 0 <= t) (ht₁ : t <= 1) : t • x in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
-/
theorem StarConvex.mem_smul (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
    x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact hs.smul_mem hx (by positivity) (inv_le_one_of_one_le₀ ht)

end AddCommGroup

end LinearOrderedField

/-!
#### Star-convex sets in an ordered space

Relates `starConvex` and `Set.ordConnected`.
-/

section OrdConnected

/-- If `s` is an order-connected set in an ordered module over an ordered semiring
and all elements of `s` are comparable with `x ∈ s`, then `s` is `StarConvex` at `x`. -/
/-
**Set.OrdConnected.starConvex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.starConvex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E
] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {x : E}
 {s : Set E} (hs : s.OrdConnected) (hx : x in s) (h : forall y in s, x <= y ∨ y 
<= x) : StarConvex 𝕜 x s
参数：hs : s.OrdConnected；hx : x in s；h : forall y in s, x <= y ∨ y <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…

--- 原说明 ---
If `s` is an order-connected set in an ordered module over an ordered semiring
and all elements of `s` are comparable with `x ∈ s`, then `s` is `StarConvex` at
 `x`.
-/
theorem Set.OrdConnected.starConvex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {x : E} {s : Set E} (hs : s.OrdConnected)
    (hx : x ∈ s) (h : ∀ y ∈ s, x ≤ y ∨ y ≤ x) : StarConvex 𝕜 x s := by
  intro y hy a b ha hb hab
  obtain hxy | hyx := h _ hy
  · refine hs.out hx hy (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        x = a • x + b • x := (Convex.combo_self hab _).symm
        _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
  · refine hs.out hy hx (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        y = a • y + b • y := (Convex.combo_self hab _).symm
        _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • x + b • x := by gcongr
      _ = x := Convex.combo_self hab _
/-
**starConvex_iff_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starConvex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing
 𝕜] {x : 𝕜} {s : Set 𝕜} (hx : x in s) : StarConvex 𝕜 x s ↔ s.OrdConnected
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ordConnected_iff_uIcc_subset_left`：ordConnected_iff_uIcc_subset_left
 (hx : x in s) : OrdConnected s ↔ forall ⦃y⦄, y in s -> [[x, y]] subseteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `segment_eq_uIcc`：segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem starConvex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ s.OrdConnected := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected

end OrdConnected

