/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topological properties of convex sets

We prove the following facts:

* `Convex.interior` : interior of a convex set is convex;
* `Convex.closure` : closure of a convex set is convex;
* `closedConvexHull_closure_eq_closedConvexHull` : the closed convex hull of the closure of a set is
  equal to the closed convex hull of the set;
* `Set.Finite.isCompact_convexHull` : convex hull of a finite set is compact;
* `Set.Finite.isClosed_convexHull` : convex hull of a finite set is closed.
-/

@[expose] public section

assert_not_exists Cardinal Norm

open Metric Bornology Set Pointwise Convex

variable {ι 𝕜 E : Type*}

namespace Real
variable {s : Set ℝ} {r ε : ℝ}

/-
**Real.closedBall_eq_segment** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：closedBall_eq_segment (hε : 0 <= ε) : closedBall r ε = segment Real (r - ε
) (r + ε)
参数：hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
-/
lemma closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]
/-
**Real.ball_eq_openSegment** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ball_eq_openSegment (hε : 0 < ε) : ball r ε = openSegment Real (r - ε) (r 
+ ε)
参数：hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `openSegment_eq_Ioo`：openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y =
 Ioo x y
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
-/
lemma ball_eq_openSegment (hε : 0 < ε) : ball r ε = openSegment ℝ (r - ε) (r + ε) := by
  rw [ball_eq_Ioo, openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]
/-
**Real.convex_iff_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convex_iff_isPreconnected : Convex Real s ↔ IsPreconnected s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `convex_iff_ordConnected`：convex_iff_ordConnected [Field 𝕜] [LinearOrder 
𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} : Convex 𝕜 s ↔ s.OrdConnected
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isPreconnected_iff_ordConnected`：isPreconnected_iff_ordConnected {s : Se
t α} : IsPreconnected s ↔ OrdConnected s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem convex_iff_isPreconnected : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

end Real

alias ⟨_, IsPreconnected.convex⟩ := Real.convex_iff_isPreconnected

/-! ### Topological vector spaces -/
section TopologicalSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {x y : E}

/-
**segment_subset_closure_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_closure_openSegment : [x -[𝕜] y] subseteq closure (openSegm
ent 𝕜 x y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `openSegment_eq_image`：openSegment_eq_image (x y : E) : openSegment 𝕜 x y
 = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem segment_subset_closure_openSegment : [x -[𝕜] y] ⊆ closure (openSegment 𝕜 x y) := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

end TopologicalSpace

section PseudoMetricSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [PseudoMetricSpace 𝕜] [OrderTopology 𝕜]
  [ProperSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

@[simp]
/-
**closure_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_openSegment (x y : E) : closure (openSegment 𝕜 x y) = [x -[𝕜] y]
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `openSegment_eq_image`：openSegment_eq_image (x y : E) : openSegment 𝕜 x y
 = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `image_closure_of_isCompact`：image_closure_of_isCompact [T2Space Y] {s : 
Set X} (hs : IsCompact (closure s)) {f : X -> Y} (hf : ContinuousOn f (closure s
)) : f '' closur…
· 使用定理 `Bornology.IsBounded.isCompact_closure`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α] [ProperSpace α], Bornology.IsBounded s → IsCompact (closu
re s)
· 使用定理 `Metric.isBounded_Ioo`：isBounded_Ioo (a b : α) : IsBounded (Ioo a b)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem closure_openSegment (x y : E) : closure (openSegment 𝕜 x y) = [x -[𝕜] y] := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact (image_closure_of_isCompact (isBounded_Ioo _ _).isCompact_closure <|
    Continuous.continuousOn <| by fun_prop).symm

end PseudoMetricSpace

section ContinuousConstSMul

variable [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for all `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `Convex.combo_interior_self_subset_interior` for a weaker version. -/
/-
**Convex.combo_interior_closure_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s
) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) : a • interior s + b • 
closure s subseteq interior s
参数：hs : Convex 𝕜 s；ha : 0 < a；hb : 0 <= b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `smul_closure_subset`：smul_closure_subset (c : M) (s : Set α) : c • closu
re s subseteq closure (c • s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.add_closure`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 :
 AddGroup G] [IsTopologicalAddGroup G] {s : Set G},   IsOpen s → ∀ (t : Set G), 
s + clos…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `subset_interior_add_left`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : AddGroup α] [ContinuousConstVAdd αᵃᵒᵖ α] {s t : Set α},   interior s + t 
⊆ interior (s …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd_op`：∀ {M : Type u_3} [inst : T
opologicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConst
VAdd Mᵃᵒᵖ M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Convex.set_combo_subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semirin
g 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] 
{s : Set E}, …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `interior_smul₀`：interior_smul₀ {c : G₀} (hc : c != 0) (s : Set α) : inte
rior (c • s) = c • interior s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for a
ll `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `Convex.combo_interior_self_subset_interior` for 
a weaker version.
-/
theorem Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • closure s ⊆ interior s :=
  interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s ⊆ interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [isOpen_interior.add_closure (b • s)]
      _ ⊆ interior (a • s + b • s) := subset_interior_add_left
      _ ⊆ interior s := interior_mono <| hs.set_combo_subset ha.le hb hab

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `Convex.combo_interior_closure_subset_interior` for a stronger version. -/
/-
**Convex.combo_interior_self_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {
a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) : a • interior s + b • s s
ubseteq interior s
参数：hs : Convex 𝕜 s；ha : 0 < a；hb : 0 <= b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Convex.combo_interior_closure_subset_interior`：Convex.combo_interior_clo
sure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 
0 <= b) (hab : a + b = 1) : a • int…

--- 原说明 ---
If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < 
a`, `0 ≤ b`,
`a + b = 1`. See also `Convex.combo_interior_closure_subset_interior` for a stro
nger version.
-/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • s ⊆ interior s :=
  calc
    a • interior s + b • s ⊆ a • interior s + b • closure s :=
      add_subset_add Subset.rfl <| image_mono subset_closure
    _ ⊆ interior s := hs.combo_interior_closure_subset_interior ha hb hab

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `Convex.combo_self_interior_subset_interior` for a weaker version. -/
/-
**Convex.combo_closure_interior_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s
) {a b : 𝕜} (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • i
nterior s subseteq interior s
参数：hs : Convex 𝕜 s；ha : 0 <= a；hb : 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convex.combo_interior_closure_subset_interior`：Convex.combo_interior_clo
sure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 
0 <= b) (hab : a + b = 1) : a • int…

--- 原说明 ---
If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for a
ll `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `Convex.combo_self_interior_subset_interior` for 
a weaker version.
-/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `Convex.combo_closure_interior_subset_interior` for a stronger version. -/
/-
**Convex.combo_self_interior_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {
a b : 𝕜} (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s s
ubseteq interior s
参数：hs : Convex 𝕜 s；ha : 0 <= a；hb : 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convex.combo_interior_self_subset_interior`：Convex.combo_interior_self_s
ubset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b
) (hab : a + b = 1) : a • interi…

--- 原说明 ---
If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ 
a`, `0 < b`,
`a + b = 1`. See also `Convex.combo_closure_interior_subset_interior` for a stro
nger version.
-/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)
/-
**Convex.combo_interior_closure_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {
x y : E} (hx : x in interior s) (hy : y in closure s) {a b : 𝕜} (ha : 0 < a) (hb
 : 0 <= b) (hab : a + b = 1) : a • x + b • y in interior s
参数：hs : Convex 𝕜 s；hx : x in interior s；hy : y in closure s；ha : 0 < a；hb : 0 <=
 b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_interior_closure_subset_interior`：Convex.combo_interior_clo
sure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 
0 <= b) (hab : a + b = 1) : a • int…
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
/-
**Convex.combo_interior_self_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y
 : E} (hx : x in interior s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) 
(hab : a + b = 1) : a • x + b • y in interior s
参数：hs : Convex 𝕜 s；hx : x in interior s；hy : y in s；ha : 0 < a；hb : 0 <= b；hab :
 a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_interior_closure_mem_interior`：Convex.combo_interior_closur
e_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in interior s) (h
y : y in closure s) {a b : 𝕜} (h…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab
/-
**Convex.combo_closure_interior_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {
x y : E} (hx : x in closure s) (hy : y in interior s) {a b : 𝕜} (ha : 0 <= a) (h
b : 0 < b) (hab : a + b = 1) : a • x + b • y in interior s
参数：hs : Convex 𝕜 s；hx : x in closure s；hy : y in interior s；ha : 0 <= a；hb : 0 <
 b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_closure_interior_subset_interior`：Convex.combo_closure_inte
rior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 <= a) (hb :
 0 < b) (hab : a + b = 1) : a • clo…
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
/-
**Convex.combo_self_interior_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y
 : E} (hx : x in s) (hy : y in interior s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 < b) 
(hab : a + b = 1) : a • x + b • y in interior s
参数：hs : Convex 𝕜 s；hx : x in s；hy : y in interior s；ha : 0 <= a；hb : 0 < b；hab :
 a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_closure_interior_mem_interior`：Convex.combo_closure_interio
r_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s) (hy
 : y in interior s) {a b : 𝕜} (h…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab
/-
**Convex.openSegment_interior_closure_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Convex.openSegment_interior_closure_subset_interior {s : Set E} (hs : Conv
ex 𝕜 s) {x y : E} (hx : x in interior s) (hy : y in closure s) : openSegment 𝕜 x
 y subseteq interior s
参数：hs : Convex 𝕜 s；hx : x in interior s；hy : y in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_interior_closure_mem_interior`：Convex.combo_interior_closur
e_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in interior s) (h
y : y in closure s) {a b : 𝕜} (h…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Convex.openSegment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab
/-
**Convex.openSegment_interior_self_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.openSegment_interior_self_subset_interior {s : Set E} (hs : Convex 
𝕜 s) {x y : E} (hx : x in interior s) (hy : y in s) : openSegment 𝕜 x y subseteq
 interior s
参数：hs : Convex 𝕜 s；hx : x in interior s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.openSegment_interior_closure_subset_interior`：Convex.openSegment_
interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in interior s) (hy : y in closure s) : o…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Convex.openSegment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)
/-
**Convex.openSegment_closure_interior_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Convex.openSegment_closure_interior_subset_interior {s : Set E} (hs : Conv
ex 𝕜 s) {x y : E} (hx : x in closure s) (hy : y in interior s) : openSegment 𝕜 x
 y subseteq interior s
参数：hs : Convex 𝕜 s；hx : x in closure s；hy : y in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.combo_closure_interior_mem_interior`：Convex.combo_closure_interio
r_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s) (hy
 : y in interior s) {a b : 𝕜} (h…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Convex.openSegment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab
/-
**Convex.openSegment_self_interior_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.openSegment_self_interior_subset_interior {s : Set E} (hs : Convex 
𝕜 s) {x y : E} (hx : x in s) (hy : y in interior s) : openSegment 𝕜 x y subseteq
 interior s
参数：hs : Convex 𝕜 s；hx : x in s；hy : y in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.openSegment_closure_interior_subset_interior`：Convex.openSegment_
closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in closure s) (hy : y in interior s) : o…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Convex.openSegment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy

section

variable [AddRightMono 𝕜]

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
/-
**Convex.add_smul_sub_mem_interior'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} 
(hx : x in closure s) (hy : y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) :
 x + t • (y - x) in interior s
参数：hs : Convex 𝕜 s；hx : x in closure s；hy : y in interior s；ht : t in Ioc (0 : 𝕜
) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convex.combo_interior_closure_mem_interior`：Convex.combo_interior_closur
e_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in interior s) (h
y : y in closure s) {a b : 𝕜} (h…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included i
n `interior s`.
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ interior s := by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel _ _)

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
/-
**Convex.add_smul_sub_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (
hx : x in s) (hy : y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) : x + t • 
(y - x) in interior s
参数：hs : Convex 𝕜 s；hx : x in s；hy : y in interior s；ht : t in Ioc (0 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.add_smul_sub_mem_interior'`：Convex.add_smul_sub_mem_interior' {s 
: Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s) (hy : y in interior s
) {t : 𝕜} (ht : t in Io…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `inter
ior s`.
-/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
/-
**Convex.add_smul_mem_interior'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx 
: x in closure s) (hy : x + y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) :
 x + t • y in interior s
参数：hs : Convex 𝕜 s；hx : x in closure s；hy : x + y in interior s；ht : t in Ioc (0
 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Convex.add_smul_sub_mem_interior'`：Convex.add_smul_sub_mem_interior' {s 
: Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s) (hy : y in interior s
) {t : 𝕜} (ht : t in Io…

--- 原说明 ---
If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t 
∈ (0, 1]`.
-/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ closure s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s := by
  simpa only [add_sub_cancel_left] using hs.add_smul_sub_mem_interior' hx hy ht

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
/-
**Convex.add_smul_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx :
 x in s) (hy : x + y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) : x + t • 
y in interior s
参数：hs : Convex 𝕜 s；hx : x in s；hy : x + y in interior s；ht : t in Ioc (0 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.add_smul_mem_interior'`：Convex.add_smul_mem_interior' {s : Set E}
 (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s) (hy : x + y in interior s) {t
 : 𝕜} (ht : t in Io…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]
`.
-/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht

end

/-- In a topological vector space, the interior of a convex set is convex. -/
/-
**Convex.interior** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : PartialOrder 𝕜]
 [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [inst_4 : TopologicalS
pace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   [ZeroLEOneClass 𝕜]
 {s : Set E}, Convex 𝕜 s → Convex 𝕜 (interior s)
参数：interior s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_openSegment_subset`：convex_iff_openSegment_subset [ZeroLEOneC
lass 𝕜] : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜
 x y subseteq s
· 使用定理 `Convex.openSegment_closure_interior_subset_interior`：Convex.openSegment_
closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in closure s) (hy : y in interior s) : o…
· 使用定理 `interior_subset_closure`：interior_subset_closure : interior s subseteq c
losure s

--- 原说明 ---
In a topological vector space, the interior of a convex set is convex.
-/
protected theorem Convex.interior [ZeroLEOneClass 𝕜] {s : Set E} (hs : Convex 𝕜 s) :
    Convex 𝕜 (interior s) :=
  convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy

/-- In a topological vector space, the closure of a convex set is convex. -/
/-
**Convex.closure** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : PartialOrder 𝕜]
 [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [inst_4 : TopologicalS
pace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   {s : Set E}, Conve
x 𝕜 s → Convex 𝕜 (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `map_mem_closure₂`：map_mem_closure₂ {f : X -> Y -> Z} {x : X} {y : Y} {s 
: Set X} {t : Set Y} {u : Set Z} (hf : Continuous (uncurry f)) (hx : x in closur
e s) (…

--- 原说明 ---
In a topological vector space, the closure of a convex set is convex.
-/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (closure s) :=
  fun x hx y hy a b ha hb hab =>
  let f : E → E → E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y ∈ closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab
/-
**convexHull_interior_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexHull_interior_subset [ZeroLEOneClass 𝕜] (s : Set E) : convexHull 𝕜 (
interior s) subseteq interior (convexHull 𝕜 s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
-/
lemma convexHull_interior_subset [ZeroLEOneClass 𝕜] (s : Set E) :
    convexHull 𝕜 (interior s) ⊆ interior (convexHull 𝕜 s) :=
  convexHull_min (interior_mono <| subset_convexHull 𝕜 s) (convex_convexHull 𝕜 s).interior
/-
**IsOpen.convexHull** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : PartialOrder 𝕜]
 [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [inst_4 : TopologicalS
pace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   [ZeroLEOneClass 𝕜]
 {s : Set E}, IsOpen s → IsOpen ((convexHull 𝕜) s)
参数：(convexHull 𝕜) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用引理 `convexHull_interior_subset`：convexHull_interior_subset [ZeroLEOneClass 𝕜
] (s : Set E) : convexHull 𝕜 (interior s) subseteq interior (convexHull 𝕜 s)
-/
protected theorem IsOpen.convexHull [ZeroLEOneClass 𝕜] {s : Set E} (hs : IsOpen s) :
    IsOpen (convexHull 𝕜 s) := by
  simpa [← subset_interior_iff_isOpen, hs.interior_eq] using convexHull_interior_subset s

end ContinuousConstSMul

section ContinuousConstSMul

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/-- A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersection with
`interior s`. -/
/-
**Convex.strictConvex'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module 𝕜 E]
 [inst_5 : TopologicalSpace E] [IsTopologicalAddGroup E]   [ContinuousConstSMul 
𝕜 E] {s : Set E},   Convex 𝕜 s → ((s \ interior s).Pairwise fun x y => ∃ c, (Aff
ineMap.lineMap x y) c ∈ interior s) → StrictConvex 𝕜 s
参数：(s \ interior s).Pairwise fun x y => ∃ c, (AffineMap.lineMap x y) c ∈ interio
r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strictConvex_iff_openSegment_subset`：strictConvex_iff_openSegment_subset
 : StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y subseteq interior 
s
· 使用定理 `Convex.openSegment_interior_self_subset_interior`：Convex.openSegment_int
erior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in in
terior s) (hy : y in s) : openSegment …
· 使用定理 `Convex.openSegment_self_interior_subset_interior`：Convex.openSegment_sel
f_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
 (hy : y in interior s) : openSegment …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `openSegment_subset_union`：openSegment_subset_union (x y : E) {z : E} (hz
 : z in range (lineMap x y : 𝕜 -> E)) : openSegment 𝕜 x y subseteq insert z (ope
nSegment 𝕜 x z…
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r

--- 原说明 ---
A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersectio
n with
`interior s`.
-/
protected theorem Convex.strictConvex' {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ∃ c : 𝕜, lineMap x y c ∈ interior s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 ?_
  intro x hx y hy hne
  by_cases hx' : x ∈ interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y ∈ interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine (openSegment_subset_union x y ⟨c, rfl⟩).trans
    (insert_subset_iff.2 ⟨hc, union_subset ?_ ?_⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]

/-- A convex set `s` is strictly convex provided that for any two distinct points `x`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection with
`interior s`. -/
/-
**Convex.strictConvex** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module 𝕜 E]
 [inst_5 : TopologicalSpace E] [IsTopologicalAddGroup E]   [ContinuousConstSMul 
𝕜 E] {s : Set E},   Convex 𝕜 s → ((s \ interior s).Pairwise fun x y => (segment 
𝕜 x y \ frontier s).Nonempty) → StrictConvex 𝕜 s
参数：(s \ interior s).Pairwise fun x y => (segment 𝕜 x y \ frontier s).Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.strictConvex'`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [ins
t_4 : _roo…
· 使用定理 `Set.Pairwise.imp_on`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, 
s.Pairwise r → (s.Pairwise fun ⦃a b⦄ => r a b → p a b) → s.Pairwise p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lineMap_mem_segment`：lineMap_mem_segment (a b : E) {t : 𝕜} (ht : t in Ic
c 0 1) : AffineMap.lineMap a b t in [a -[𝕜] b]

--- 原说明 ---
A convex set `s` is strictly convex provided that for any two distinct points `x
`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection 
with
`interior s`.
-/
protected theorem Convex.strictConvex {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ([x -[𝕜] y] \ frontier s).Nonempty) :
    StrictConvex 𝕜 s := by
  refine hs.strictConvex' <| h.imp_on fun x hx y hy _ => ?_
  simp only [segment_eq_image_lineMap, ← self_sdiff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine ⟨c, hs.segment_subset hx.1 hy.1 ?_, hcs⟩
  exact lineMap_mem_segment 𝕜 x y hc

end ContinuousConstSMul

section ContinuousSMul

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousSMul 𝕜 E]

/-
**Convex.closure_interior_eq_closure_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Convex.closure_interior_eq_closure_of_nonempty_interior {s : Set E} (hs : 
Convex 𝕜 s) (hs' : (interior s).Nonempty) : closure (interior s) = closure s
参数：hs : Convex 𝕜 s；hs' : (interior s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Convex.openSegment_interior_closure_subset_interior`：Convex.openSegment_
interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in interior s) (hy : y in closure s) : o…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `segment_subset_closure_openSegment`：segment_subset_closure_openSegment :
 [x -[𝕜] y] subseteq closure (openSegment 𝕜 x y)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `right_mem_segment`：right_mem_segment (x y : E) : y in [x -[𝕜] y]
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem Convex.closure_interior_eq_closure_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : closure (interior s) = closure s :=
  subset_antisymm (closure_mono interior_subset)
    fun _ h ↦ closure_mono (hs.openSegment_interior_closure_subset_interior hs'.choose_spec h)
      (segment_subset_closure_openSegment (right_mem_segment ..))
/-
**Convex.interior_closure_eq_interior_of_nonempty_interior** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Convex.interior_closure_eq_interior_of_nonempty_interior {s : Set E} (hs :
 Convex 𝕜 s) (hs' : (interior s).Nonempty) : interior (closure s) = interior s
参数：hs : Convex 𝕜 s；hs' : (interior s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Filter.Eventually.exists_gt`：∀ {α : Type u_1} [inst : TopologicalSpace α
] [inst_1 : Preorder α] {a : α} [(nhdsWithin a (Set.Ioi a)).NeBot]   {p : α → Pr
op}, (∀ᶠ (x : α) …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `AffineMap.lineMap_continuous`：lineMap_continuous {p q : P} : Continuous 
(lineMap p q : R ->ᵃ[R] P)
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Convex.openSegment_interior_closure_subset_interior`：Convex.openSegment_
interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in interior s) (hy : y in closure s) : o…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `image_openSegment`：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' o
penSegment 𝕜 a b = openSegment 𝕜 (f a) (f b)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Ioo_subset_openSegment`：Ioo_subset_openSegment : Ioo x y subseteq openSe
gment 𝕜 x y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
（共 31 条，此处仅展示前 30 条）
-/
theorem Convex.interior_closure_eq_interior_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : interior (closure s) = interior s := by
  refine subset_antisymm ?_ (interior_mono subset_closure)
  intro y hy
  rcases hs' with ⟨x, hx⟩
  have h := AffineMap.lineMap_apply_one (k := 𝕜) x y
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h |>.eventually_mem
    (mem_interior_iff_mem_nhds.1 hy) |>.exists_gt
  apply hs.openSegment_interior_closure_subset_interior hx ht
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := 𝕜) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

end ContinuousSMul

section TopologicalSpace

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-
**convex_closed_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_closed_sInter {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s ∧ Is
Closed s) : Convex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S)
参数：Set E；h : forall s in S, Convex 𝕜 s ∧ IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_sInter`：starConvex_sInter {S : Set (Set E)} (h : forall s in 
S, StarConvex 𝕜 x s) : StarConvex 𝕜 x (⋂₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem convex_closed_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s ∧ IsClosed s) :
    Convex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
  ⟨fun _ hx => starConvex_sInter fun _ hs => (h _ hs).1 <| hx _ hs,
    isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜) in
/-- The convex closed hull of a set `s` is the minimal convex closed set that includes `s`. -/
@[simps! isClosed]
/-
**closedConvexHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：closedConvexHull : ClosureOperator (Set E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `convex_closed_sInter`：convex_closed_sInter {S : Set (Set E)} (h : forall
 s in S, Convex 𝕜 s ∧ IsClosed s) : Convex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S)

--- 原说明 ---
The convex closed hull of a set `s` is the minimal convex closed set that includ
es `s`.
-/
def closedConvexHull : ClosureOperator (Set E) := .ofCompletePred (fun s => Convex 𝕜 s ∧ IsClosed s)
  fun _ ↦ convex_closed_sInter
/-
**convex_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_closedConvexHull {s : Set E} : Convex 𝕜 (closedConvexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem convex_closedConvexHull {s : Set E} :
    Convex 𝕜 (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).1
/-
**isClosed_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_closedConvexHull {s : Set E} : IsClosed (closedConvexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem isClosed_closedConvexHull {s : Set E} :
    IsClosed (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).2
/-
**subset_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_closedConvexHull {s : Set E} : s subseteq closedConvexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem subset_closedConvexHull {s : Set E} : s ⊆ closedConvexHull 𝕜 s :=
  (closedConvexHull 𝕜).le_closure s
/-
**closure_subset_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_closedConvexHull {s : Set E} : closure s subseteq closedCon
vexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `subset_closedConvexHull`：subset_closedConvexHull {s : Set E} : s subsete
q closedConvexHull 𝕜 s
· 使用定理 `isClosed_closedConvexHull`：isClosed_closedConvexHull {s : Set E} : IsClo
sed (closedConvexHull 𝕜 s)
-/
theorem closure_subset_closedConvexHull {s : Set E} : closure s ⊆ closedConvexHull 𝕜 s :=
  closure_minimal subset_closedConvexHull isClosed_closedConvexHull
/-
**closedConvexHull_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedConvexHull_min {s t : Set E} (hst : s subseteq t) (h_conv : Convex 𝕜
 t) (h_closed : IsClosed t) : closedConvexHull 𝕜 s subseteq t
参数：hst : s subseteq t；h_conv : Convex 𝕜 t；h_closed : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
theorem closedConvexHull_min {s t : Set E} (hst : s ⊆ t) (h_conv : Convex 𝕜 t)
    (h_closed : IsClosed t) : closedConvexHull 𝕜 s ⊆ t :=
  (closedConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩
/-
**convexHull_subset_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_subset_closedConvexHull {s : Set E} : (convexHull 𝕜) s subseteq
 (closedConvexHull 𝕜) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `subset_closedConvexHull`：subset_closedConvexHull {s : Set E} : s subsete
q closedConvexHull 𝕜 s
· 使用定理 `convex_closedConvexHull`：convex_closedConvexHull {s : Set E} : Convex 𝕜 
(closedConvexHull 𝕜 s)
-/
theorem convexHull_subset_closedConvexHull {s : Set E} :
    (convexHull 𝕜) s ⊆ (closedConvexHull 𝕜) s :=
  convexHull_min subset_closedConvexHull convex_closedConvexHull

@[simp]
/-
**closedConvexHull_closure_eq_closedConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedConvexHull_closure_eq_closedConvexHull {s : Set E} : closedConvexHul
l 𝕜 (closure s) = closedConvexHull 𝕜 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `closure_subset_closedConvexHull`：closure_subset_closedConvexHull {s : Se
t E} : closure s subseteq closedConvexHull 𝕜 s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closedConvexHull_closure_eq_closedConvexHull {s : Set E} :
    closedConvexHull 𝕜 (closure s) = closedConvexHull 𝕜 s :=
  subset_antisymm (by
    simpa using ((closedConvexHull 𝕜).monotone (closure_subset_closedConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedConvexHull 𝕜).monotone subset_closure)

end TopologicalSpace

section ContinuousConstSMul

variable [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-
**closedConvexHull_eq_closure_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedConvexHull_eq_closure_convexHull {s : Set E} : closedConvexHull 𝕜 s 
= closure (convexHull 𝕜 s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closedConvexHull_min`：closedConvexHull_min {s t : Set E} (hst : s subset
eq t) (h_conv : Convex 𝕜 t) (h_closed : IsClosed t) : closedConvexHull 𝕜 s subse
teq t
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `convexHull_subset_closedConvexHull`：convexHull_subset_closedConvexHull {
s : Set E} : (convexHull 𝕜) s subseteq (closedConvexHull 𝕜) s
· 使用定理 `isClosed_closedConvexHull`：isClosed_closedConvexHull {s : Set E} : IsClo
sed (closedConvexHull 𝕜 s)
-/
theorem closedConvexHull_eq_closure_convexHull {s : Set E} :
    closedConvexHull 𝕜 s = closure (convexHull 𝕜 s) := subset_antisymm
  (closedConvexHull_min (subset_trans (subset_convexHull 𝕜 s) subset_closure)
    (Convex.closure (convex_convexHull 𝕜 s)) isClosed_closure)
  (closure_minimal convexHull_subset_closedConvexHull isClosed_closedConvexHull)

end ContinuousConstSMul

section Compact
variable (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- Convex hull of a finite set is compact. -/
/-
**Set.Finite.isCompact_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) : IsCompact (c
onvexHull 𝕜 s)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.convexHull_eq_image`：Set.Finite.convexHull_eq_image {E : Type
*} [AddCommGroup E] [Module R E] {s : Set E} (hs : s.Finite) : convexHull R s = 
haveI
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `isCompact_stdSimplex`：isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrdere
dAddMonoid 𝕜] : IsCompact (stdSimplex 𝕜 ι)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LinearMap.continuous_on_pi`：LinearMap.continuous_on_pi {ι : Type*} {R : 
Type*} {M : Type*} [Finite ι] [Semiring R] [TopologicalSpace R] [AddCommMonoid M
] [Module R M] […
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G

--- 原说明 ---
Convex hull of a finite set is compact.
-/
theorem Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) :
    IsCompact (convexHull 𝕜 s) := by
  rw [hs.convexHull_eq_image]
  let := hs.fintype
  exact (isCompact_stdSimplex 𝕜 s).image (LinearMap.continuous_on_pi _)

/-- Convex hull of a finite set is closed. -/
/-
**Set.Finite.isClosed_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) : I
sClosed (convexHull 𝕜 s)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Set.Finite.isCompact_convexHull`：Set.Finite.isCompact_convexHull {s : Se
t E} (hs : s.Finite) : IsCompact (convexHull 𝕜 s)

--- 原说明 ---
Convex hull of a finite set is closed.
-/
theorem Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) :
    IsClosed (convexHull 𝕜 s) :=
  (hs.isCompact_convexHull 𝕜).isClosed

end Compact

section ContinuousSMul
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

open AffineMap

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
/-
**Convex.closure_subset_image_homothety_interior_of_one_lt** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs :
 Convex Real s) {x : E} (hx : x in interior s) (t : Real) (ht : 1 < t) : closure
 s subseteq homothety x t '' interior s
参数：hs : Convex Real s；hx : x in interior s；t : Real；ht : 1 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Convex.openSegment_interior_closure_subset_interior`：Convex.openSegment_
interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in interior s) (hy : y in closure s) : o…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image_lineMap`：openSegment_eq_image_lineMap (x y : E) : o
penSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Set.inv_Ioi₀`：inv_Ioi₀ (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `AffineMap.homothety_eq_lineMap`：homothety_eq_lineMap (c : P1) (r : k) (p
 : P1) : homothety c r p = lineMap c p r
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `AffineEquiv.apply_symm_apply`：apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂
) : e (e.symm p) = p

--- 原说明 ---
If we dilate the interior of a convex set about a point in its interior by a sca
le `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped ab
out `x`.
-/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ homothety x t '' interior s := by
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap, ← inv_one, ← inv_Ioi₀ (zero_lt_one' ℝ), ← image_inv_eq_inv,
    image_image, homothety_eq_lineMap]
  exact mem_image_of_mem _ ht

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
/-
**Convex.closure_subset_interior_image_homothety_of_one_lt** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs :
 Convex Real s) {x : E} (hx : x in interior s) (t : Real) (ht : 1 < t) : closure
 s subseteq interior (homothety x t '' s)
参数：hs : Convex Real s；hx : x in interior s；t : Real；ht : 1 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Convex.closure_subset_image_homothety_interior_of_one_lt`：Convex.closure
_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex Real s) {x :
 E} (hx : x in interior s) (t : Real) (ht : 1 …
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用定理 `AffineMap.homothety_isOpenMap`：homothety_isOpenMap (x : P) (t : R) (ht :
 t != 0) : IsOpenMap homothety x t
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If we dilate a convex set about a point in its interior by a scale `t > 1`, the 
interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped ab
out `x`.
-/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ interior (homothety x t '' s) :=
  (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans <|
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
/-
**Convex.subset_interior_image_homothety_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex 
Real s) {x : E} (hx : x in interior s) (t : Real) (ht : 1 < t) : s subseteq inte
rior (homothety x t '' s)
参数：hs : Convex Real s；hx : x in interior s；t : Real；ht : 1 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Convex.closure_subset_interior_image_homothety_of_one_lt`：Convex.closure
_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex Real s) {x :
 E} (hx : x in interior s) (t : Real) (ht : 1 …

--- 原说明 ---
If we dilate a convex set about a point in its interior by a scale `t > 1`, the 
interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped ab
out `x`.
-/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) : s ⊆ interior (homothety x t '' s) :=
  subset_closure.trans <| hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

end ContinuousSMul

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]

open scoped Topology
open Filter

/-
**Convex.nontrivial_iff_nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.nontrivial_iff_nonempty_interior {s : Set 𝕜} (hs : Convex 𝕜 s) : s.
Nontrivial ↔ (interior s).Nonempty
参数：hs : Convex 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_lt_sup`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊓ b < a ⊔ b ↔
 a ≠ b
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `segment_eq_Icc'`：segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) 
(max x y)
· 使用引理 `Set.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in s)
 : s = {a} ∨ s.Nontrivial
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `interior_singleton`：interior_singleton (x : X) [NeBot (𝓝[!=] x)] : inter
ior {x} = (∅ : Set X)
· 使用定理 `instNeBotNhdsWithinComplSetSingletonOfNontrivial`：∀ {α : Type u_1} [inst
 : TopologicalSpace α] [inst_1 : LinearOrder α] [OrderTopology α] [DenselyOrdere
d α] (x : α)   [Nontrivial α], (nhdsWi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Convex.nontrivial_iff_nonempty_interior {s : Set 𝕜} (hs : Convex 𝕜 s) :
    s.Nontrivial ↔ (interior s).Nonempty := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    have hs' := Nonempty.mono <| interior_mono <| hs.segment_subset hx hy
    rw [segment_eq_Icc', interior_Icc, nonempty_Ioo, inf_lt_sup] at hs'
    exact hs' h
  · rintro ⟨x, hx⟩
    rcases eq_singleton_or_nontrivial (interior_subset hx) with rfl | h
    · rw [interior_singleton] at hx
      exact hx.elim
    · exact h
/-
**Convex.Ioo_subset_of_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.Ioo_subset_of_mem_closure {s : Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜} (
has : a in closure s) (hbs : b in closure s) : Ioo a b subseteq s
参数：hs : Convex 𝕜 s；has : a in closure s；hbs : b in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Subsingleton.closure`：Set.Subsingleton.closure [T1Space X] {s : Set 
X} (hs : s.Subsingleton) : (closure s).Subsingleton
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_Ioo`：interior_Ioo : interior (Ioo a b) = Ioo a b
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Ioo_subset_openSegment`：Ioo_subset_openSegment : Ioo x y subseteq openSe
gment 𝕜 x y
· 使用定理 `Convex.openSegment_subset`：Convex.openSegment_subset (h : Convex 𝕜 s) {x
 y : E} (hx : x in s) (hy : y in s) : openSegment 𝕜 x y subseteq s
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `Convex.interior_closure_eq_interior_of_nonempty_interior`：Convex.interio
r_closure_eq_interior_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s) (hs' : 
(interior s).Nonempty) : interior (closure s) …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Convex.nontrivial_iff_nonempty_interior`：Convex.nontrivial_iff_nonempty_
interior {s : Set 𝕜} (hs : Convex 𝕜 s) : s.Nontrivial ↔ (interior s).Nonempty
（共 31 条，此处仅展示前 30 条）
-/
lemma Convex.Ioo_subset_of_mem_closure {s : Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜}
    (has : a ∈ closure s) (hbs : b ∈ closure s) :
    Ioo a b ⊆ s := by
  cases subsingleton_or_nontrivial s with
  | inl hs_sub =>
    simp only [subsingleton_coe] at hs_sub
    simp [hs_sub.closure has hbs]
  | inr h' =>
    simp only [nontrivial_coe_sort] at h'
    calc Ioo a b
    _ = interior (Ioo a b) := interior_Ioo.symm
    _ ⊆ interior (openSegment 𝕜 a b) := interior_mono <| Ioo_subset_openSegment
    _ ⊆ interior (closure s) := interior_mono <| hs.closure.openSegment_subset has hbs
    _ = interior s := hs.interior_closure_eq_interior_of_nonempty_interior <|
      hs.nontrivial_iff_nonempty_interior.1 h'
    _ ⊆ s := interior_subset
/-
**Convex.nhdsWithin_inter_Iio_eq_nhdsLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.nhdsWithin_inter_Iio_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜
} (has : a in closure s) (h' : (s inter Iio a).Nonempty) : 𝓝[s inter Iio a] a = 
𝓝[<] a
参数：hs : Convex 𝕜 s；has : a in closure s；h' : (s inter Iio a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset`：mem_nhdsLT_iff_exists_Ioo_subset [NoMi
nOrder α] {a : α} {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subsete
q s
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Convex.Ioo_subset_of_mem_closure`：Convex.Ioo_subset_of_mem_closure {s : 
Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜} (has : a in closure s) (hbs : b in closure s)
 : Ioo a b subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma Convex.nhdsWithin_inter_Iio_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a ∈ closure s) (h' : (s ∩ Iio a).Nonempty) :
    𝓝[s ∩ Iio a] a = 𝓝[<] a := by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure (subset_closure hbs) has
/-
**Convex.nhdsWithin_inter_Ioi_eq_nhdsGT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.nhdsWithin_inter_Ioi_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜
} (has : a in closure s) (h' : (s inter Ioi a).Nonempty) : 𝓝[s inter Ioi a] a = 
𝓝[>] a
参数：hs : Convex 𝕜 s；has : a in closure s；h' : (s inter Ioi a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsGT_iff_exists_Ioo_subset`：mem_nhdsGT_iff_exists_Ioo_subset [NoMa
xOrder α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subsete
q s
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Convex.Ioo_subset_of_mem_closure`：Convex.Ioo_subset_of_mem_closure {s : 
Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜} (has : a in closure s) (hbs : b in closure s)
 : Ioo a b subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma Convex.nhdsWithin_inter_Ioi_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a ∈ closure s) (h' : (s ∩ Ioi a).Nonempty) :
    𝓝[s ∩ Ioi a] a = 𝓝[>] a := by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure has (subset_closure hbs)
/-
**Convex.nhdsWithin_sdiff_eq_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.nhdsWithin_sdiff_eq_nhdsNE {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (h
as : a in closure s) (h_Iio : (s inter Iio a).Nonempty) (h_Ioi : (s inter Ioi a)
.Nonempty) : 𝓝[s \ {a}] a = 𝓝[!=] a
参数：hs : Convex 𝕜 s；has : a in closure s；h_Iio : (s inter Iio a).Nonempty；h_Ioi :
 (s inter Ioi a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Convex.nhdsWithin_inter_Iio_eq_nhdsLT`：Convex.nhdsWithin_inter_Iio_eq_nh
dsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (has : a in closure s) (h' : (s inter
 Iio a).Nonempty) : 𝓝[s int…
· 使用引理 `Convex.nhdsWithin_inter_Ioi_eq_nhdsGT`：Convex.nhdsWithin_inter_Ioi_eq_nh
dsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (has : a in closure s) (h' : (s inter
 Ioi a).Nonempty) : 𝓝[s int…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsNE {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a ∈ closure s) (h_Iio : (s ∩ Iio a).Nonempty) (h_Ioi : (s ∩ Ioi a).Nonempty) :
    𝓝[s \ {a}] a = 𝓝[≠] a := by
  rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, nhdsWithin_union, nhdsWithin_union]
  simp [hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsNE := Convex.nhdsWithin_sdiff_eq_nhdsNE
/-
**Convex.nhdsWithin_sdiff_eq_nhdsLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.nhdsWithin_sdiff_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (h
as : a in closure s) (h_Iio : (s inter Iio a).Nonempty) (h_Ioi : s inter Ioi a =
 ∅) : 𝓝[s \ {a}] a = 𝓝[<] a
参数：hs : Convex 𝕜 s；has : a in closure s；h_Iio : (s inter Iio a).Nonempty；h_Ioi :
 s inter Ioi a = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Convex.nhdsWithin_inter_Iio_eq_nhdsLT`：Convex.nhdsWithin_inter_Iio_eq_nh
dsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (has : a in closure s) (h' : (s inter
 Iio a).Nonempty) : 𝓝[s int…
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a ∈ closure s) (h_Iio : (s ∩ Iio a).Nonempty) (h_Ioi : s ∩ Ioi a = ∅) :
    𝓝[s \ {a}] a = 𝓝[<] a := by
  rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, nhdsWithin_union]
  simp [h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsLT := Convex.nhdsWithin_sdiff_eq_nhdsLT
/-
**Convex.nhdsWithin_sdiff_eq_nhdsGT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.nhdsWithin_sdiff_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (h
as : a in closure s) (h_Iio : s inter Iio a = ∅) (h_Ioi : (s inter Ioi a).Nonemp
ty) : 𝓝[s \ {a}] a = 𝓝[>] a
参数：hs : Convex 𝕜 s；has : a in closure s；h_Iio : s inter Iio a = ∅；h_Ioi : (s int
er Ioi a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用引理 `Convex.nhdsWithin_inter_Ioi_eq_nhdsGT`：Convex.nhdsWithin_inter_Ioi_eq_nh
dsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜} (has : a in closure s) (h' : (s inter
 Ioi a).Nonempty) : 𝓝[s int…
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a ∈ closure s) (h_Iio : s ∩ Iio a = ∅) (h_Ioi : (s ∩ Ioi a).Nonempty) :
    𝓝[s \ {a}] a = 𝓝[>] a := by
  rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, nhdsWithin_union]
  simp [h_Iio, hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsGT := Convex.nhdsWithin_sdiff_eq_nhdsGT

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-
**sdiff_singleton_eventually_mem_nhds_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sdiff_singleton_eventually_mem_nhds_left {s : Set 𝕜} {a : 𝕜}
    (h : ∀ x ∈ closure s, Ioo x a ⊆ s) : ∀ᶠ (x : 𝕜) in 𝓝[s ∩ Iio a] a, s \ {a} ∈ 𝓝 x := by
  rcases eq_empty_or_nonempty (s ∩ Iio a) with hs' | ⟨b, hbs, hba⟩
  · simp [hs']
  have : Ioo b a ⊆ s := h b (subset_closure hbs)
  apply eventually_of_mem (U := Ioo b a) ?_ fun x hx ↦ ?_
  · exact mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hba, fun _ ⟨h₁, _, h₂⟩ ↦ ⟨h₁, h₂⟩⟩
  · exact mem_nhds_iff.2 ⟨Ioo b a, subset_sdiff_singleton this right_notMem_Ioo, isOpen_Ioo, hx⟩
/-
**Convex.sdiff_singleton_eventually_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.sdiff_singleton_eventually_mem_nhds {s : Set 𝕜} (hs : Convex 𝕜 s) (
a : 𝕜) : forallᶠ x in 𝓝[s \ {a}] a, s \ {a} in 𝓝 x
参数：hs : Convex 𝕜 s；a : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `_private.Mathlib.Analysis.Convex.Topology.0.sdiff_singleton_eventually_m
em_nhds_left`：∀ {𝕜 : Type u_4} [inst : LinearOrder 𝕜] [inst_1 : TopologicalSpace
 𝕜] [OrderTopology 𝕜] {s : Set 𝕜} {a : 𝕜},   (∀ x ∈ closure s, Set.Ioo x a…
· 使用引理 `Convex.Ioo_subset_of_mem_closure`：Convex.Ioo_subset_of_mem_closure {s : 
Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜} (has : a in closure s) (hbs : b in closure s)
 : Ioo a b subseteq s
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem Convex.sdiff_singleton_eventually_mem_nhds {s : Set 𝕜} (hs : Convex 𝕜 s) (a : 𝕜) :
    ∀ᶠ x in 𝓝[s \ {a}] a, s \ {a} ∈ 𝓝 x := by
  rcases eq_or_neBot (𝓝[s \ {a}] a) with h | has
  · rw [h]
    exact eventually_bot
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  conv in 𝓝[s \ {a}] a => rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left]
  rw [nhdsWithin_union, eventually_sup]
  exact ⟨sdiff_singleton_eventually_mem_nhds_left fun x hx ↦ hs.Ioo_subset_of_mem_closure hx has,
    sdiff_singleton_eventually_mem_nhds_left (𝕜 := 𝕜ᵒᵈ) fun x hx z hz ↦
      hs.Ioo_subset_of_mem_closure has hx hz.symm⟩

@[deprecated (since := "2026-06-03")]
alias Convex.diff_singleton_eventually_mem_nhds := Convex.sdiff_singleton_eventually_mem_nhds

end LinearOrderedField

namespace Affine.Simplex

variable {𝕜 V P : Type*}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [Module 𝕜 V] [ContinuousSMul 𝕜 V] [AddTorsor V P]
  [TopologicalSpace P] [IsTopologicalAddTorsor P]

set_option backward.isDefEq.respectTransparency false in
/-- The closed interior of a simplex is compact. -/
/-
**Affine.Simplex.isCompact_closedInterior** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：isCompact_closedInterior {n : Nat} (s : Simplex 𝕜 P n) : IsCompact s.close
dInterior
参数：s : Simplex 𝕜 P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.closedInterior_map`：closedInterior_map {n : Nat} (s : Sim
plex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) : (s.map f hf).closedI
nterior = f '' s.closed…
· 使用定理 `Affine.Simplex.convexHull_eq_closedInterior`：∀ {𝕜 : Type u_1} {V : Type 
u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsOrderedRing 𝕜] [inst_3 : AddCo
mmGroup V]   [inst_4 : _root_.Mod…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Set.Finite.isCompact_convexHull`：Set.Finite.isCompact_convexHull {s : Se
t E} (hs : s.Finite) : IsCompact (convexHull 𝕜 s)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Homeomorph.isCompact_image`：isCompact_image {s : Set X} (h : X ≃ₜ Y) : I
sCompact (h '' s) ↔ IsCompact s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.vaddConst_symm_apply`：∀ {V : Type u_1} {P : Type u_2} [inst :
 AddGroup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : 
TopologicalSpace P] […
· 使用定理 `AffineEquiv.vaddConst_symm_apply`：∀ (k : Type u_1) {P₁ : Type u_2} {V₁ :
 Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module 
k V₁] [inst_3 : AddTor…

--- 原说明 ---
The closed interior of a simplex is compact.
-/
theorem isCompact_closedInterior {n : ℕ} (s : Simplex 𝕜 P n) : IsCompact s.closedInterior := by
  suffices IsCompact ((AffineEquiv.vaddConst 𝕜 (s.points 0)).symm.toAffineMap ''
      s.closedInterior) by
    apply (Homeomorph.vaddConst (s.points 0)).symm.isCompact_image.mp
    simpa
  rw [← s.closedInterior_map (AffineEquiv.injective _), ← convexHull_eq_closedInterior]
  exact (Set.finite_range _).isCompact_convexHull 𝕜

/-- The closed interior of a simplex is a closed set. -/
/-
**Affine.Simplex.isClosed_closedInterior** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：isClosed_closedInterior [T2Space P] {n : Nat} (s : Simplex 𝕜 P n) : IsClos
ed s.closedInterior
参数：s : Simplex 𝕜 P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Affine.Simplex.isCompact_closedInterior`：isCompact_closedInterior {n : N
at} (s : Simplex 𝕜 P n) : IsCompact s.closedInterior

--- 原说明 ---
The closed interior of a simplex is a closed set.
-/
theorem isClosed_closedInterior [T2Space P] {n : ℕ} (s : Simplex 𝕜 P n) :
    IsClosed s.closedInterior :=
  s.isCompact_closedInterior.isClosed

end Affine.Simplex

