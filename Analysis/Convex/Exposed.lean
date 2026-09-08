/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Order.OrderClosed

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functoriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`IsExposed.isExtreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `IsExposed 𝕜 A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `IsExposed.isExtreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating exposed sets and points to the intrinsic frontier.
-/

@[expose] public section

open Affine Set

section PreorderSemiring

variable (𝕜 : Type*) {E : Type*} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `IsExposed 𝕜 A B`. -/
/-
**IsExposed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsExposed (A B : Set E) : Prop
参数：A B : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `B` is exposed with respect to `A` iff it maximizes some functional over `
A` (and contains
all points maximizing it). Written `IsExposed 𝕜 A B`.
-/
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty → ∃ l : StrongDual 𝕜 E, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }

end PreorderSemiring

section OrderedRing

variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {l : StrongDual 𝕜 E} {A B C : Set E} {x : E}

/-- A useful way to build exposed sets from intersecting `A` with half-spaces (modelled by an
inequality with a functional). -/
/-
**ContinuousLinearMap.toExposed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.toExposed (l : StrongDual 𝕜 E) (A : Set E) : Set E
参数：l : StrongDual 𝕜 E；A : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A useful way to build exposed sets from intersecting `A` with half-spaces (model
led by an
inequality with a functional).
-/
def ContinuousLinearMap.toExposed (l : StrongDual 𝕜 E) (A : Set E) : Set E :=
  { x ∈ A | ∀ y ∈ A, l y ≤ l x }
/-
**ContinuousLinearMap.toExposed.isExposed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun _ => ⟨l, rfl⟩
/-
**isExposed_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExposed_empty : IsExposed 𝕜 A ∅
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isExposed_empty : IsExposed 𝕜 A ∅ := fun ⟨_, hx⟩ => by
  exfalso
  exact hx

namespace IsExposed

/-
**IsExposed.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] {A B : Set E},   IsExposed 𝕜 A B → B ⊆ A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A := by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1

@[refl]
/-
**IsExposed.refl** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] (A : Set E), IsExposed 𝕜 A A
参数：A : Set E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem refl (A : Set E) : IsExposed 𝕜 A A := fun ⟨_, _⟩ =>
  ⟨0, Subset.antisymm (fun _ hx => ⟨hx, fun _ _ => le_refl 0⟩) fun _ hx => hx.1⟩
/-
**IsExposed.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] {A B : Set E},   IsExposed 𝕜 A B → IsExpos
ed 𝕜 B A → A = B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsExposed.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpa
ce 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [
inst_4…
-/
protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.subset.antisymm hB.subset

/-! `IsExposed` is *not* transitive: Consider a (topologically) open cube with vertices
`A₀₀₀, ..., A₁₁₁` and add to it the triangle `A₀₀₀A₀₀₁A₀₁₀`. Then `A₀₀₁A₀₁₀` is an exposed subset
of `A₀₀₀A₀₀₁A₀₁₀` which is an exposed subset of the cube, but `A₀₀₁A₀₁₀` is not itself an exposed
subset of the cube. -/

/-
**IsExposed.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] {A B C : Set E},   IsExposed 𝕜 A C → B ⊆ A
 → C ⊆ B → IsExposed 𝕜 B C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`IsExposed` is *not* transitive: Consider a (topologically) open cube with verti
ces
`A₀₀₀, ..., A₁₁₁` and add to it the triangle `A₀₀₀A₀₀₁A₀₁₀`. Then `A₀₀₁A₀₁₀` is 
an exposed subset
of `A₀₀₀A₀₀₁A₀₁₀` which is an exposed subset of the cube, but `A₀₀₁A₀₁₀` is not 
itself an exposed
subset of the cube.
-/
protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
    ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩

/-- If `B` is a nonempty exposed subset of `A`, then `B` is the intersection of `A` with some closed
half-space. The converse is *not* true. It would require that the corresponding open half-space
doesn't intersect `A`. -/
/-
**IsExposed.eq_inter_halfSpace'** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：eq_inter_halfSpace' {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty
) : exists l : StrongDual 𝕜 E, exists a, B = { x in A | a <= l x }
参数：hAB : IsExposed 𝕜 A B；hB : B.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `B` is a nonempty exposed subset of `A`, then `B` is the intersection of `A` 
with some closed
half-space. The converse is *not* true. It would require that the corresponding 
open half-space
doesn't intersect `A`.
-/
theorem eq_inter_halfSpace' {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty) :
    ∃ l : StrongDual 𝕜 E, ∃ a, B = { x ∈ A | a ≤ l x } := by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact ⟨l, l w, Subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
    ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩

/-- For nontrivial `𝕜`, if `B` is an exposed subset of `A`, then `B` is the intersection of `A` with
some closed half-space. The converse is *not* true. It would require that the corresponding open
half-space doesn't intersect `A`. -/
/-
**IsExposed.eq_inter_halfSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：eq_inter_halfSpace [IsOrderedRing 𝕜] [Nontrivial 𝕜] {A B : Set E} (hAB : I
sExposed 𝕜 A B) : exists l : StrongDual 𝕜 E, exists a, B = { x in A | a <= l x }
参数：hAB : IsExposed 𝕜 A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsExposed.eq_inter_halfSpace'`：eq_inter_halfSpace' {A B : Set E} (hAB : 
IsExposed 𝕜 A B) (hB : B.Nonempty) : exists l : StrongDual 𝕜 E, exists a, B = { 
x in A | a <= l x }

--- 原说明 ---
For nontrivial `𝕜`, if `B` is an exposed subset of `A`, then `B` is the intersec
tion of `A` with
some closed half-space. The converse is *not* true. It would require that the co
rresponding open
half-space doesn't intersect `A`.
-/
theorem eq_inter_halfSpace [IsOrderedRing 𝕜] [Nontrivial 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B) :
    ∃ l : StrongDual 𝕜 E, ∃ a, B = { x ∈ A | a ≤ l x } := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine ⟨0, 1, ?_⟩
    rw [eq_comm, eq_empty_iff_forall_notMem]
    rintro x ⟨-, h⟩
    rw [zero_apply] at h
    have : ¬(1 : 𝕜) ≤ 0 := not_le_of_gt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfSpace' hB
/-
**IsExposed.inter** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] [IsOrderedRing 𝕜]   [ContinuousAdd 𝕜] {A B
 C : Set E}, IsExposed 𝕜 A B → IsExposed 𝕜 A C → IsExposed 𝕜 A (B ∩ C)
参数：B ∩ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem inter [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {A B C : Set E} (hB : IsExposed 𝕜 A B)
    (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B ∩ C) := by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine ⟨l₁ + l₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine ⟨⟨hxA, fun y hy => ?_⟩, hxA, fun y hy => ?_⟩
  · exact
      (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
  · exact
      (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))
/-
**IsExposed.sInter** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：sInter [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.No
nempty) (hAF : forall B in F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F)
参数：Set E；hF : F.Nonempty；hAF : forall B in F, IsExposed 𝕜 A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Finset.not_nonempty_empty`：not_nonempty_empty : ¬(∅ : Finset α).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsExposed.inter`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpac
e 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [i
nst_4…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem sInter [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.Nonempty)
    (hAF : ∀ B ∈ F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F) := by
  induction F using Finset.induction with
  | empty => exfalso; exact Finset.not_nonempty_empty hF
  | insert C F _ hF' =>
    rw [Finset.coe_insert, sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    · rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hAF C (Finset.mem_singleton_self C)
    · exact (hAF C (Finset.mem_insert_self C F)).inter
        (hF' hFnemp fun B hB => hAF B (Finset.mem_insert_of_mem hB))
/-
**IsExposed.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：inter_left (hC : IsExposed 𝕜 A C) (hCB : C subseteq B) : IsExposed 𝕜 (A in
ter B) C
参数：hC : IsExposed 𝕜 A C；hCB : C subseteq B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsExposed.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpa
ce 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [
inst_4…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inter_left (hC : IsExposed 𝕜 A C) (hCB : C ⊆ B) : IsExposed 𝕜 (A ∩ B) C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
    fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩
/-
**IsExposed.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：inter_right (hC : IsExposed 𝕜 B C) (hCA : C subseteq A) : IsExposed 𝕜 (A i
nter B) C
参数：hC : IsExposed 𝕜 B C；hCA : C subseteq A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsExposed.inter_left`：inter_left (hC : IsExposed 𝕜 A C) (hCB : C subsete
q B) : IsExposed 𝕜 (A inter B) C
-/
theorem inter_right (hC : IsExposed 𝕜 B C) (hCA : C ⊆ A) : IsExposed 𝕜 (A ∩ B) C := by
  rw [inter_comm]
  exact hC.inter_left hCA
/-
**IsExposed.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] [OrderClosedTopology 𝕜]   {A B : Set E}, I
sExposed 𝕜 A B → IsClosed A → IsClosed B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsExposed.eq_inter_halfSpace'`：eq_inter_halfSpace' {A B : Set E} (hAB : 
IsExposed 𝕜 A B) (hB : B.Nonempty) : exists l : StrongDual 𝕜 E, exists a, B = { 
x in A | a <= l x }
· 使用定理 `IsClosed.isClosed_le`：IsClosed.isClosed_le [TopologicalSpace β] {f g : β
 -> α} {s : Set β} (hs : IsClosed s) (hf : ContinuousOn f s) (hg : ContinuousOn 
g s) : IsC…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
protected theorem isClosed [OrderClosedTopology 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
    (hA : IsClosed A) : IsClosed B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfSpace' hB
  exact hA.isClosed_le continuousOn_const l.continuous.continuousOn
/-
**IsExposed.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [inst_4 : Topological
Space E] [inst_5 : _root_.Module 𝕜 E] [OrderClosedTopology 𝕜]   [T2Space E] {A B
 : Set E}, IsExposed 𝕜 A B → IsCompact A → IsCompact B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsExposed.isClosed`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalS
pace 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E]
 [inst_4…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsExposed.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpa
ce 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [
inst_4…
-/
protected theorem isCompact [OrderClosedTopology 𝕜] [T2Space E] {A B : Set E}
    (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) : IsCompact B :=
  hA.of_isClosed_subset (hAB.isClosed hA.isClosed) hAB.subset

end IsExposed

variable (𝕜) in
/-- A point is exposed with respect to `A` iff there exists a hyperplane whose intersection with
`A` is exactly that point. -/
/-
**Set.exposedPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.exposedPoints (A : Set E) : Set E
参数：A : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point is exposed with respect to `A` iff there exists a hyperplane whose inter
section with
`A` is exactly that point.
-/
def Set.exposedPoints (A : Set E) : Set E :=
  { x ∈ A | ∃ l : StrongDual 𝕜 E, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) }
/-
**exposed_point_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exposed_point_def : x in A.exposedPoints 𝕜 ↔ x in A ∧ exists l : StrongDua
l 𝕜 E, forall y in A, l y <= l x ∧ (l x <= l y -> y = x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exposed_point_def :
    x ∈ A.exposedPoints 𝕜 ↔ x ∈ A ∧ ∃ l :
    StrongDual 𝕜 E, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) := Iff.rfl
/-
**exposedPoints_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exposedPoints_subset : A.exposedPoints 𝕜 subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exposedPoints_subset : A.exposedPoints 𝕜 ⊆ A := fun _ hx => hx.1

@[simp]
/-
**exposedPoints_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exposedPoints_empty : (∅ : Set E).exposedPoints 𝕜 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `exposedPoints_subset`：exposedPoints_subset : A.exposedPoints 𝕜 subseteq 
A
-/
theorem exposedPoints_empty : (∅ : Set E).exposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposedPoints_subset

/-- Exposed points exactly correspond to exposed singletons. -/
/-
**mem_exposedPoints_iff_exposed_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_exposedPoints_iff_exposed_singleton : x in A.exposedPoints 𝕜 ↔ IsExpos
ed 𝕜 A {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Exposed points exactly correspond to exposed singletons.
-/
theorem mem_exposedPoints_iff_exposed_singleton : x ∈ A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x} := by
  use fun ⟨hxA, l, hl⟩ _ =>
    ⟨l,
      Eq.symm <|
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l, fun y hy =>
      ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩

end OrderedRing

section LinearOrderedRing

variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜]
  [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

namespace IsExposed

/-
**IsExposed.convex** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : LinearOrder 𝕜]   [IsStrictOrderedRing 𝕜] [inst_4 : AddCommMonoid E
] [inst_5 : TopologicalSpace E] [inst_6 : _root_.Module 𝕜 E]   {A B : Set E}, Is
Exposed 𝕜 A B → Convex 𝕜 A → Convex 𝕜 B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `convex_empty`：convex_empty : Convex 𝕜 (∅ : Set E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ConcaveOn.convex_ge`：ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) 
: Convex 𝕜 ({ x in s | r <= f x })
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `LinearMap.concaveOn`：LinearMap.concaveOn (f : E ->ₗ[𝕜] β) {s : Set E} (h
s : Convex 𝕜 s) : ConcaveOn 𝕜 s f
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
protected theorem convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩ ha hb hab).2⟩
/-
**IsExposed.isExtreme** 是 Mathlib 中的一个定理，位于命名空间 `IsExposed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpace 𝕜] [inst_1 : Ring
 𝕜] [inst_2 : LinearOrder 𝕜]   [IsStrictOrderedRing 𝕜] [inst_4 : AddCommMonoid E
] [inst_5 : TopologicalSpace E] [inst_6 : _root_.Module 𝕜 E]   {A B : Set E}, Is
Exposed 𝕜 A B → IsExtreme 𝕜 A B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExposed.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : TopologicalSpa
ce 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E] [
inst_4…
· 使用定理 `LinearMap.convexOn`：LinearMap.convexOn (f : E ->ₗ[𝕜] β) {s : Set E} (hs 
: Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ConvexOn.le_left_of_right_le`：ConvexOn.le_left_of_right_le (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hyz : f y <= f z) …
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem isExtreme (hAB : IsExposed 𝕜 A B) : IsExtreme 𝕜 A B := by
  refine ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => ?_⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.toLinearMap.convexOn convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine ⟨hx₁A, fun y hy => ?_⟩
  rw [hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)]
  exact hxB.2 y hy

end IsExposed

/-
**exposedPoints_subset_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exposedPoints_subset_extremePoints : A.exposedPoints 𝕜 subseteq A.extremeP
oints 𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtreme.mem_extremePoints`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜
 E] {A : Set E} {…
· 使用定理 `IsExposed.isExtreme`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Topological
Space 𝕜] [inst_1 : Ring 𝕜] [inst_2 : LinearOrder 𝕜]   [IsStrictOrderedRing 𝕜] [i
nst_4 : A…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_exposedPoints_iff_exposed_singleton`：mem_exposedPoints_iff_exposed_s
ingleton : x in A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x}
-/
theorem exposedPoints_subset_extremePoints : A.exposedPoints 𝕜 ⊆ A.extremePoints 𝕜 := fun _ hx =>
  (mem_exposedPoints_iff_exposed_singleton.1 hx).isExtreme.mem_extremePoints

end LinearOrderedRing

