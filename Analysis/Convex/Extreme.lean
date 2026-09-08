/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`IsExposed.isExtreme`).

## Main declarations

* `IsExtreme 𝕜 A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `Set.extremePoints 𝕜 A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `Convex.mem_extremePoints_iff_convex_sdiff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating extreme sets and points to the intrinsic frontier.
-/

@[expose] public section


open Function Module Set Affine

variable {𝕜 E F ι : Type*} {M : ι → Type*}

section SMul

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`.

Our definition only requires that the left endpoint of the segment lies in `B`,
but by symmetry of open segments, the right endpoint must also lie in `B`.
See `IsExtreme.right_mem_of_mem_openSegment`. -/
@[mk_iff]
/-
**IsExtreme** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} → [Semiring 𝕜] → [PartialOrder 𝕜] → [Add
CommMonoid E] → [SMul 𝕜 E] → Set E → Set E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belo
ng to open
segments whose ends are in `B`.

Our definition only requires that the left endpoint of the segment lies in `B`,
but by symmetry of open segments, the right endpoint must also lie in `B`.
See `IsExtreme.right_mem_of_mem_openSegment`.
-/
structure IsExtreme (A B : Set E) : Prop where
  subset : B ⊆ A
  left_mem_of_mem_openSegment : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A →
    ∀ ⦃z⦄, z ∈ B → z ∈ openSegment 𝕜 x y → x ∈ B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `openSegment x x`. -/
/-
**Set.extremePoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.extremePoints (A : Set E) : Set E
参数：A : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x` is an extreme point of a set `A` if `x` belongs to no open segment w
ith ends in
`A`, except for the obvious `openSegment x x`.
-/
def Set.extremePoints (A : Set E) : Set E :=
  {x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x}

@[refl]
/-
**IsExtreme.refl** 是 Mathlib 中的一个定理，位于命名空间 `IsExtreme`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] (A : Set E), IsExtreme 𝕜 A 
A
参数：𝕜 : Type u_1；A : Set E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨Subset.rfl, fun _ hx₁A _ _ _ _ _ ↦ hx₁A⟩

variable {𝕜} {A B C : Set E} {x : E}
/-
**IsExtreme.rfl** 是 Mathlib 中的一个定理，位于命名空间 `IsExtreme`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A : Set E}, IsExtreme 𝕜 A 
A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtreme.refl`：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : Semiring 𝕜] [ins
t_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] (A : Set 
E), …
-/
protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A
/-
**IsExtreme.right_mem_of_mem_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtreme.right_mem_of_mem_openSegment (h : IsExtreme 𝕜 A B) {y z : E} (hx
 : x in A) (hy : y in A) (hz : z in B) (hzxy : z in openSegment 𝕜 x y) : y in B
参数：h : IsExtreme 𝕜 A B；hx : x in A；hy : y in A；hz : z in B；hzxy : z in openSegme
nt 𝕜 x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_symm`：openSegment_symm (x y : E) : openSegment 𝕜 x y = openS
egment 𝕜 y x
-/
theorem IsExtreme.right_mem_of_mem_openSegment (h : IsExtreme 𝕜 A B) {y z : E} (hx : x ∈ A)
    (hy : y ∈ A) (hz : z ∈ B) (hzxy : z ∈ openSegment 𝕜 x y) : y ∈ B :=
  h.left_mem_of_mem_openSegment hy hx hz <| by rwa [openSegment_symm]

@[trans]
/-
**IsExtreme.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsExtreme`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B C : Set E}, IsExtreme 
𝕜 A B → IsExtreme 𝕜 B C → IsExtreme 𝕜 A C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
· 使用定理 `IsExtreme.right_mem_of_mem_openSegment`：IsExtreme.right_mem_of_mem_openS
egment (h : IsExtreme 𝕜 A B) {y z : E} (hx : x in A) (hy : y in A) (hz : z in B)
 (hzxy : z in openSegment 𝕜 …
-/
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
    IsExtreme 𝕜 A C := by
  refine ⟨hBC.subset.trans hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxC hx ↦ ?_⟩
  exact hBC.left_mem_of_mem_openSegment
    (hAB.left_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx)
    (hAB.right_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx) hxC hx
/-
**IsExtreme.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `IsExtreme`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E], Std.Antisymm (IsExtreme 𝕜)
参数：IsExtreme 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
-/
protected theorem IsExtreme.antisymm : Std.Antisymm (IsExtreme 𝕜 : Set E → Set E → Prop) :=
  ⟨fun _ _ hAB hBA ↦ Subset.antisymm hBA.1 hAB.1⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (Set E) (IsExtreme 𝕜) where
  refl := IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  __ := IsExtreme.antisymm
/-
**IsExtreme.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) : IsExtrem
e 𝕜 A (B inter C)
参数：hAB : IsExtreme 𝕜 A B；hAC : IsExtreme 𝕜 A C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
-/
theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) :
    IsExtreme 𝕜 A (B ∩ C) := by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  exact ⟨hAB.left_mem_of_mem_openSegment hx₁A hx₂A hxB hx,
    hAC.left_mem_of_mem_openSegment hx₁A hx₂A hxC hx⟩
/-
**IsExtreme.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsExtreme`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B C : Set E}, IsExtreme 
𝕜 A C → B ⊆ A → C ⊆ B → IsExtreme 𝕜 B C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
-/
protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
    IsExtreme 𝕜 B C :=
  ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx ↦ hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩
/-
**isExtreme_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι -> Set E} (hAF : forall i
 : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i)
参数：hAF : forall i : ι, IsExtreme 𝕜 A (F i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
-/
theorem isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι → Set E}
    (hAF : ∀ i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i) := by
  inhabit ι
  refine ⟨iInter_subset_of_subset default (hAF default).1, fun x₁ hx₁A x₂ hx₂A x hxF hx ↦ ?_⟩
  rw [mem_iInter] at hxF ⊢
  exact fun i ↦ (hAF i).2 hx₁A hx₂A (hxF i) hx
/-
**isExtreme_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : forall B in F,
 IsExtreme 𝕜 A B) : IsExtreme 𝕜 A (⋂ B in F, B)
参数：Set E；hF : F.Nonempty；hA : forall B in F, IsExtreme 𝕜 A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isExtreme_iInter`：isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι -> Se
t E} (hAF : forall i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂ B ∈ F, B) := by
  have := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F ↦ hA _ i.2
/-
**isExtreme_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : forall B in F,
 IsExtreme 𝕜 A B) : IsExtreme 𝕜 A (⋂₀ F)
参数：Set E；hF : F.Nonempty；hAF : forall B in F, IsExtreme 𝕜 A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `isExtreme_biInter`：isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty)
 (hA : forall B in F, IsExtreme 𝕜 A B) : IsExtreme 𝕜 A (⋂ B in F, B)
-/
theorem isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂₀ F) := by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF

/-- A point `x` is an extreme point of a set `A`
iff `x ∈ A` and for any `x₁`, `x₂` such that `x` belongs to the open segment `(x₁, x₂)`,
we have `x₁ = x` and `x₂ = x`.

We used to use the RHS as the definition of `extremePoints`.
However, the conclusion `x₂ = x` is redundant,
so we changed the definition to the RHS of `mem_extremePoints_iff_left`. -/
/-
**mem_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_extremePoints : x in A.extremePoints 𝕜 ↔ x in A ∧ forallᵉ (x₁ in A) (x
₂ in A), x in openSegment 𝕜 x₁ x₂ -> x₁ = x ∧ x₂ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_symm`：openSegment_symm (x y : E) : openSegment 𝕜 x y = openS
egment 𝕜 y x

--- 原说明 ---
A point `x` is an extreme point of a set `A`
iff `x ∈ A` and for any `x₁`, `x₂` such that `x` belongs to the open segment `(x
₁, x₂)`,
we have `x₁ = x` and `x₂ = x`.

We used to use the RHS as the definition of `extremePoints`.
However, the conclusion `x₂ = x` is redundant,
so we changed the definition to the RHS of `mem_extremePoints_iff_left`.
-/
theorem mem_extremePoints : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x := by
  refine ⟨fun h ↦ ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx ↦ ⟨h.2 hx₁ hx₂ hx, ?_⟩⟩,
    fun h ↦ ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx ↦ (h.2 x₁ hx₁ x₂ hx₂ hx).1⟩⟩
  apply h.2 hx₂ hx₁
  rwa [openSegment_symm]

/-- A point `x` is an extreme point of a set `A`
iff `x ∈ A` and for any `x₁`, `x₂` such that `x` belongs to the open segment `(x₁, x₂)`,
we have `x₁ = x`. -/
/-
**mem_extremePoints_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_extremePoints_iff_left : x in A.extremePoints 𝕜 ↔ x in A ∧ forall x₁ i
n A, forall x₂ in A, x in openSegment 𝕜 x₁ x₂ -> x₁ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point `x` is an extreme point of a set `A`
iff `x ∈ A` and for any `x₁`, `x₂` such that `x` belongs to the open segment `(x
₁, x₂)`,
we have `x₁ = x`.
-/
theorem mem_extremePoints_iff_left : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ x₁ ∈ A, ∀ x₂ ∈ A, x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x :=
  .rfl

/-- `x` is an extreme point to `A` iff `{x}` is an extreme set of `A`. -/
/-
**isExtreme_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A : Set E} {x : E}, IsExtr
eme 𝕜 A {x} ↔ x ∈ Set.extremePoints 𝕜 A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`x` is an extreme point to `A` iff `{x}` is an extreme set of `A`.
-/
@[simp] lemma isExtreme_singleton : IsExtreme 𝕜 A {x} ↔ x ∈ A.extremePoints 𝕜 := by
  simp [isExtreme_iff, extremePoints]

alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton
/-
**extremePoints_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_subset : A.extremePoints 𝕜 subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem extremePoints_subset : A.extremePoints 𝕜 ⊆ A :=
  fun _ hx ↦ hx.1

@[simp]
/-
**extremePoints_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
-/
theorem extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extremePoints_subset

@[simp]
/-
**extremePoints_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x} :=
  extremePoints_subset.antisymm <| singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ _ _ ↦ hx₁⟩
/-
**inter_extremePoints_subset_extremePoints_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：inter_extremePoints_subset_extremePoints_of_subset (hBA : B subseteq A) : 
B inter A.extremePoints 𝕜 subseteq B.extremePoints 𝕜
参数：hBA : B subseteq A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inter_extremePoints_subset_extremePoints_of_subset (hBA : B ⊆ A) :
    B ∩ A.extremePoints 𝕜 ⊆ B.extremePoints 𝕜 :=
  fun _ ⟨hxB, hxA⟩ ↦ ⟨hxB, fun _ hx₁ _ hx₂ hx ↦ hxA.2 (hBA hx₁) (hBA hx₂) hx⟩
/-
**IsExtreme.extremePoints_subset_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) : B.e
xtremePoints 𝕜 subseteq A.extremePoints 𝕜
参数：hAB : IsExtreme 𝕜 A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsExtreme.trans`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [in
st_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B C :
 Set …
-/
theorem IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 ⊆ A.extremePoints 𝕜 :=
  fun _ ↦ by simpa only [← isExtreme_singleton] using hAB.trans
/-
**IsExtreme.extremePoints_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) : B.extremePoints 𝕜 = B
 inter A.extremePoints 𝕜
参数：hAB : IsExtreme 𝕜 A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsExtreme.extremePoints_subset_extremePoints`：IsExtreme.extremePoints_su
bset_extremePoints (hAB : IsExtreme 𝕜 A B) : B.extremePoints 𝕜 subseteq A.extrem
ePoints 𝕜
· 使用定理 `inter_extremePoints_subset_extremePoints_of_subset`：inter_extremePoints_
subset_extremePoints_of_subset (hBA : B subseteq A) : B inter A.extremePoints 𝕜 
subseteq B.extremePoints 𝕜
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
-/
theorem IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 = B ∩ A.extremePoints 𝕜 :=
  Subset.antisymm (fun _ hx ↦ ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)

@[nontriviality]
/-
**Set.extremePoints_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.extremePoints_eq_self [Subsingleton E] (A : Set E) : Set.extremePoints
 𝕜 A = A
参数：A : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma Set.extremePoints_eq_self [Subsingleton E] (A : Set E) : Set.extremePoints 𝕜 A = A :=
  subset_antisymm extremePoints_subset fun _ h ↦ ⟨h, fun _ _ _ _ _ ↦ Subsingleton.elim ..⟩

end SMul

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [AddCommGroup F] [∀ i, AddCommGroup (M i)]
  [Module 𝕜 E] [Module 𝕜 F] [∀ i, Module 𝕜 (M i)] {A B : Set E}

/-
**IsExtreme.convex_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtreme.convex_sdiff [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtrem
e 𝕜 A B) : Convex 𝕜 (A \ B)
参数：hA : Convex 𝕜 A；hAB : IsExtreme 𝕜 A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_openSegment_subset`：convex_iff_openSegment_subset [ZeroLEOneC
lass 𝕜] : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜
 x y subseteq s
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Convex.openSegment_subset`：Convex.openSegment_subset (h : Convex 𝕜 s) {x
 y : E} (hx : x in s) (hy : y in s) : openSegment 𝕜 x y subseteq s
· 使用定理 `IsExtreme.left_mem_of_mem_openSegment`：∀ {𝕜 : Type u_1} {E : Type u_2} [
inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_
3 : SMul 𝕜 E] {A B : Set E}…
-/
theorem IsExtreme.convex_sdiff [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) :
    Convex 𝕜 (A \ B) :=
  convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx ↦
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB ↦ hx₁B (hAB.2 hx₁A hx₂A hxB hx)⟩

@[deprecated (since := "2026-06-03")] alias IsExtreme.convex_diff := IsExtreme.convex_sdiff

@[simp]
/-
**extremePoints_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_prod (s : Set E) (t : Set F) : (s ×ˢ t).extremePoints 𝕜 = s.
extremePoints 𝕜 ×ˢ t.extremePoints 𝕜
参数：s : Set E；t : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.image_mk_openSegment_left`：image_mk_openSegment_left (x₁ x₂ : E) (y
 : F) : (fun x => (x, y)) '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.image_mk_openSegment_right`：image_mk_openSegment_right (x : E) (y₁ 
y₂ : F) : (fun y => (x, y)) '' openSegment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y
₂)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
-/
theorem extremePoints_prod (s : Set E) (t : Set F) :
    (s ×ˢ t).extremePoints 𝕜 = s.extremePoints 𝕜 ×ˢ t.extremePoints 𝕜 := by
  ext ⟨x, y⟩
  refine (and_congr_right fun hx ↦ ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩).trans and_and_and_comm
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    ext
    · exact h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congrArg Prod.fst hx'⟩
    · exact h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congrArg Prod.snd hx'⟩
  · rintro x₁ hx₁ x₂ hx₂ hx_fst
    refine congrArg Prod.fst (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) ?_)
    rw [← Prod.image_mk_openSegment_left]
    exact mem_image_of_mem _ hx_fst
  · rintro x₁ hx₁ x₂ hx₂ hx_snd
    refine congrArg Prod.snd (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) ?_)
    rw [← Prod.image_mk_openSegment_right]
    exact mem_image_of_mem _ hx_snd

@[simp]
/-
**extremePoints_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_pi (s : forall i, Set (M i)) : (univ.pi s).extremePoints 𝕜 =
 univ.pi fun i => (s i).extremePoints 𝕜
参数：s : forall i, Set (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.image_update_openSegment`：image_update_openSegment (i : ι) (x₁ x₂ : M
 i) (y : forall i, M i) : update y i '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (upd
ate y i x₁) (upda…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem extremePoints_pi (s : ∀ i, Set (M i)) :
    (univ.pi s).extremePoints 𝕜 = univ.pi fun i ↦ (s i).extremePoints 𝕜 := by
  classical
  ext x
  simp only [mem_extremePoints_iff_left, mem_univ_pi, @forall_and ι]
  refine and_congr_right fun hx ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    rw [← update_self i x₁ x, h (update x i x₁) _ (update x i x₂)]
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
    · rw [← Pi.image_update_openSegment]
      exact ⟨_, hi, update_eq_self _ _⟩
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, rfl⟩
    ext i
    exact h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, rfl⟩

end OrderedSemiring

section OrderedRing
variable {L : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [EquivLike L E F] [LinearEquivClass L 𝕜 E F]

/-
**image_extremePoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：image_extremePoints (f : L) (s : Set E) : f '' extremePoints 𝕜 s = extreme
Points 𝕜 (f '' s)
参数：f : L；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `image_openSegment`：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' o
penSegment 𝕜 a b = openSegment 𝕜 (f a) (f b)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_extremePoints (f : L) (s : Set E) :
    f '' extremePoints 𝕜 s = extremePoints 𝕜 (f '' s) := by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : ∀ x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_image, (EquivLike.injective f).eq_iff, ← this]

end OrderedRing

section LinearOrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] {A : Set E} {x : E}

/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
/-
**mem_extremePoints_iff_forall_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_extremePoints_iff_forall_segment : x in A.extremePoints 𝕜 ↔ x in A ∧ f
orallᵉ (x₁ in A) (x₂ in A), x in segment 𝕜 x₁ x₂ -> x₁ = x ∨ x₂ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_extremePoints`：mem_extremePoints : x in A.extremePoints 𝕜 ↔ x in A ∧
 forallᵉ (x₁ in A) (x₂ in A), x in openSegment 𝕜 x₁ x₂ -> x₁ = x ∧ x₂ = x
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `insert_endpoints_openSegment`：insert_endpoints_openSegment (x y : E) : i
nsert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y]
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `left_mem_openSegment_iff`：left_mem_openSegment_iff [DenselyOrdered 𝕜] [I
sTorsionFree 𝕜 E] : x in openSegment 𝕜 x y ↔ x = y
· 使用定理 `right_mem_openSegment_iff`：right_mem_openSegment_iff [DenselyOrdered 𝕜] 
[IsTorsionFree 𝕜 E] : y in openSegment 𝕜 x y ↔ x = y

--- 原说明 ---
A useful restatement using `segment`: `x` is an extreme point iff the only (clos
ed) segments
that contain it are those with `x` as one of their endpoints.
-/
theorem mem_extremePoints_iff_forall_segment : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x₂ = x := by
  rw [mem_extremePoints]
  refine and_congr_right fun hxA ↦ forall₄_congr fun x₁ h₁ x₂ h₂ ↦ ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ _ hx) with (rfl | rfl)
    exacts [⟨rfl, (left_mem_openSegment_iff.1 hx).symm⟩, ⟨right_mem_openSegment_iff.1 hx, rfl⟩]
/-
**Convex.mem_extremePoints_iff_convex_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_extremePoints_iff_convex_sdiff (hA : Convex 𝕜 A) : x in A.extre
mePoints 𝕜 ↔ x in A ∧ Convex 𝕜 (A \ {x})
参数：hA : Convex 𝕜 A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsExtreme.convex_sdiff`：IsExtreme.convex_sdiff [IsOrderedRing 𝕜] (hA : C
onvex 𝕜 A) (hAB : IsExtreme 𝕜 A B) : Convex 𝕜 (A \ B)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isExtreme_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜]
 [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A :
 Set E} {…
· 使用定理 `mem_extremePoints_iff_forall_segment`：mem_extremePoints_iff_forall_segme
nt : x in A.extremePoints 𝕜 ↔ x in A ∧ forallᵉ (x₁ in A) (x₂ in A), x in segment
 𝕜 x₁ x₂ -> x₁ = x ∨ x₂ = …
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem Convex.mem_extremePoints_iff_convex_sdiff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A ∧ Convex 𝕜 (A \ {x}) := by
  use fun hx ↦ ⟨hx.1, (isExtreme_singleton.2 hx).convex_sdiff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx ↦ ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ ↦ h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, fun hx₂ ↦ h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_convex_diff := Convex.mem_extremePoints_iff_convex_sdiff
/-
**Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff (hA : Convex 𝕜 A) 
: x in A.extremePoints 𝕜 ↔ x in A \ convexHull 𝕜 (A \ {x})
参数：hA : Convex 𝕜 A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.mem_extremePoints_iff_convex_sdiff`：Convex.mem_extremePoints_iff_
convex_sdiff (hA : Convex 𝕜 A) : x in A.extremePoints 𝕜 ↔ x in A ∧ Convex 𝕜 (A \
 {x})
· 使用定理 `Convex.convex_remove_iff_notMem_convexHull_remove`：Convex.convex_remove_
iff_notMem_convexHull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) : Convex 𝕜 (s
 \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x})
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A \ convexHull 𝕜 (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_convex_sdiff, hA.convex_remove_iff_notMem_convexHull_remove,
    mem_sdiff]

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_mem_diff_convexHull_diff :=
  Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
/-
**extremePoints_convexHull_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 subsete
q A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.mem_extremePoints_iff_convex_sdiff`：Convex.mem_extremePoints_iff_
convex_sdiff (hA : Convex 𝕜 A) : x in A.extremePoints 𝕜 ↔ x in A ∧ Convex 𝕜 (A \
 {x})
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 ⊆ A := by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_sdiff] at hx
  by_contra h
  exact (convexHull_min (subset_sdiff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl

end LinearOrderedRing

