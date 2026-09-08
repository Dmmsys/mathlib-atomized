/-
Copyright (c) 2023 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier, interior and closure of a set in a normed additive torsor.
These are also known as relative frontier, interior, closure.

The intrinsic frontier/interior/closure of a set `s` is the frontier/interior/closure of `s`
considered as a set in its affine span.

The intrinsic interior is in general greater than the topological interior, the intrinsic frontier
in general less than the topological frontier, and the intrinsic closure in cases of interest the
same as the topological closure.

## Definitions

* `intrinsicInterior`: Intrinsic interior
* `intrinsicFrontier`: Intrinsic frontier
* `intrinsicClosure`: Intrinsic closure

## Results

The main results are:
* `AffineIsometry.intrinsicInterior_image`/`AffineIsometry.intrinsicFrontier_image`/
  `AffineIsometry.intrinsicClosure_image`: Intrinsic interiors/frontiers/closures commute with
  taking the image under an affine isometry.
* `Set.Nonempty.intrinsicInterior`: The intrinsic interior of a nonempty convex set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].

## TODO

* `IsClosed s → IsExtreme 𝕜 s (intrinsicFrontier 𝕜 s)`
* `x ∈ s → y ∈ intrinsicInterior 𝕜 s → openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s`
-/

@[expose] public section

open AffineSubspace Set Topology
open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section AddTorsor

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
/-
**intrinsicInterior** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intrinsicInterior (s : Set P) : Set P
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic interior of a set is its interior considered as a set in its affin
e span.
-/
def intrinsicInterior (s : Set P) : Set P :=
  (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
/-
**intrinsicFrontier** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intrinsicFrontier (s : Set P) : Set P
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic frontier of a set is its frontier considered as a set in its affin
e span.
-/
def intrinsicFrontier (s : Set P) : Set P :=
  (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/-- The intrinsic closure of a set is its closure considered as a set in its affine span. -/
/-
**intrinsicClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intrinsicClosure (s : Set P) : Set P
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic closure of a set is its closure considered as a set in its affine 
span.
-/
def intrinsicClosure (s : Set P) : Set P :=
  (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

variable {𝕜}

@[simp]
/-
**mem_intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_intrinsicInterior : x in intrinsicInterior 𝕜 s ↔ exists y, y in interi
or ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_intrinsicInterior :
    x ∈ intrinsicInterior 𝕜 s ↔ ∃ y, y ∈ interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
/-
**mem_intrinsicFrontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_intrinsicFrontier : x in intrinsicFrontier 𝕜 s ↔ exists y, y in fronti
er ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_intrinsicFrontier :
    x ∈ intrinsicFrontier 𝕜 s ↔ ∃ y, y ∈ frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
/-
**mem_intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_intrinsicClosure : x in intrinsicClosure 𝕜 s ↔ exists y, y in closure 
((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_intrinsicClosure :
    x ∈ intrinsicClosure 𝕜 s ↔ ∃ y, y ∈ closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _
/-
**intrinsicInterior_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_subset : intrinsicInterior 𝕜 s subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem intrinsicInterior_subset : intrinsicInterior 𝕜 s ⊆ s :=
  image_subset_iff.2 interior_subset
/-
**intrinsicFrontier_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_subset (hs : IsClosed s) : intrinsicFrontier 𝕜 s subsete
q s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `IsClosed.frontier_subset`：∀ {X : Type u} [inst : TopologicalSpace X] {s 
: Set X}, IsClosed s → frontier s ⊆ s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem intrinsicFrontier_subset (hs : IsClosed s) : intrinsicFrontier 𝕜 s ⊆ s :=
  image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset
/-
**intrinsicFrontier_subset_intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_subset_intrinsicClosure : intrinsicFrontier 𝕜 s subseteq
 intrinsicClosure 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `frontier_subset_closure`：frontier_subset_closure : frontier s subseteq c
losure s
-/
theorem intrinsicFrontier_subset_intrinsicClosure : intrinsicFrontier 𝕜 s ⊆ intrinsicClosure 𝕜 s :=
  image_mono frontier_subset_closure
/-
**subset_intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_intrinsicClosure : s subseteq intrinsicClosure 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem subset_intrinsicClosure : s ⊆ intrinsicClosure 𝕜 s :=
  fun x hx => ⟨⟨x, subset_affineSpan _ _ hx⟩, subset_closure hx, rfl⟩

@[simp]
/-
**intrinsicInterior_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_empty : intrinsicInterior 𝕜 (∅ : Set P) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_empty`：interior_empty : interior (∅ : Set X) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicInterior_empty : intrinsicInterior 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicInterior]

@[simp]
/-
**intrinsicFrontier_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_empty : intrinsicFrontier 𝕜 (∅ : Set P) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_empty`：frontier_empty : frontier (∅ : Set X) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicFrontier_empty : intrinsicFrontier 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicFrontier]

@[simp]
/-
**intrinsicClosure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_empty : intrinsicClosure 𝕜 (∅ : Set P) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicClosure_empty : intrinsicClosure 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicClosure]

@[simp]
/-
**intrinsicClosure_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_nonempty : (intrinsicClosure 𝕜 s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `intrinsicClosure_empty`：intrinsicClosure_empty : intrinsicClosure 𝕜 (∅ :
 Set P) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `subset_intrinsicClosure`：subset_intrinsicClosure : s subseteq intrinsicC
losure 𝕜 s
-/
theorem intrinsicClosure_nonempty : (intrinsicClosure 𝕜 s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicClosure_empty,
    Nonempty.mono subset_intrinsicClosure⟩

alias ⟨Set.Nonempty.ofIntrinsicClosure, Set.Nonempty.intrinsicClosure⟩ := intrinsicClosure_nonempty

@[simp]
/-
**intrinsicInterior_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_singleton (x : P) : intrinsicInterior 𝕜 ({x} : Set P) = 
{x}
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.preimage_coe_affineSpan_singleton`：preimage_coe_affineSpa
n_singleton (x : P) : ((↑) : affineSpan k ({x} : Set P) -> P) ⁻¹' {x} = univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicInterior_singleton (x : P) : intrinsicInterior 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicInterior, preimage_coe_affineSpan_singleton, interior_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

@[simp]
/-
**intrinsicFrontier_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_singleton (x : P) : intrinsicFrontier 𝕜 ({x} : Set P) = 
∅
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicFrontier.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [
inst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 
: Topologica…
· 使用定理 `AffineSubspace.preimage_coe_affineSpan_singleton`：preimage_coe_affineSpa
n_singleton (x : P) : ((↑) : affineSpan k ({x} : Set P) -> P) ⁻¹' {x} = univ
· 使用定理 `frontier_univ`：frontier_univ : frontier (univ : Set X) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
theorem intrinsicFrontier_singleton (x : P) : intrinsicFrontier 𝕜 ({x} : Set P) = ∅ := by
  rw [intrinsicFrontier, preimage_coe_affineSpan_singleton, frontier_univ, image_empty]

@[simp]
/-
**intrinsicClosure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_singleton (x : P) : intrinsicClosure 𝕜 ({x} : Set P) = {x
}
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.preimage_coe_affineSpan_singleton`：preimage_coe_affineSpa
n_singleton (x : P) : ((↑) : affineSpan k ({x} : Set P) -> P) ⁻¹' {x} = univ
· 使用定理 `closure_univ`：closure_univ : closure (univ : Set X) = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicClosure_singleton (x : P) : intrinsicClosure 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicClosure, preimage_coe_affineSpan_singleton, closure_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

/-!
Note that neither `intrinsicInterior` nor `intrinsicFrontier` is monotone.
-/


/-
**intrinsicClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_mono (h : s subseteq t) : intrinsicClosure 𝕜 s subseteq i
ntrinsicClosure 𝕜 t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t

--- 原说明 ---
Note that neither `intrinsicInterior` nor `intrinsicFrontier` is monotone.
-/
theorem intrinsicClosure_mono (h : s ⊆ t) : intrinsicClosure 𝕜 s ⊆ intrinsicClosure 𝕜 t := by
  refine image_subset_iff.2 fun x hx => ?_
  refine ⟨Set.inclusion (affineSpan_mono _ h) x, ?_, rfl⟩
  refine (continuous_inclusion (affineSpan_mono _ h)).closure_preimage_subset _ (closure_mono ?_ hx)
  exact fun y hy => h hy
/-
**interior_subset_intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_subset_intrinsicInterior : interior s subseteq intrinsicInterior 
𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem interior_subset_intrinsicInterior : interior s ⊆ intrinsicInterior 𝕜 s :=
  fun x hx => ⟨⟨x, subset_affineSpan _ _ <| interior_subset hx⟩,
    preimage_interior_subset_interior_preimage continuous_subtype_val hx, rfl⟩
/-
**intrinsicClosure_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_subset_closure : intrinsicClosure 𝕜 s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem intrinsicClosure_subset_closure : intrinsicClosure 𝕜 s ⊆ closure s :=
  image_subset_iff.2 <| continuous_subtype_val.closure_preimage_subset _
/-
**intrinsicFrontier_subset_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_subset_frontier : intrinsicFrontier 𝕜 s subseteq frontie
r s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Continuous.frontier_preimage_subset`：Continuous.frontier_preimage_subset
 (hf : Continuous f) (t : Set Y) : frontier (f ⁻¹' t) subseteq f ⁻¹' frontier t
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem intrinsicFrontier_subset_frontier : intrinsicFrontier 𝕜 s ⊆ frontier s :=
  image_subset_iff.2 <| continuous_subtype_val.frontier_preimage_subset _
/-
**intrinsicClosure_subset_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_subset_affineSpan : intrinsicClosure 𝕜 s subseteq affineS
pan 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem intrinsicClosure_subset_affineSpan : intrinsicClosure 𝕜 s ⊆ affineSpan 𝕜 s :=
  (image_subset_range _ _).trans Subtype.range_coe.subset

@[simp]
/-
**intrinsicClosure_sdiff_intrinsicFrontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_sdiff_intrinsicFrontier (s : Set P) : intrinsicClosure 𝕜 
s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_sdiff_frontier`：closure_sdiff_frontier (s : Set X) : closure s \
 frontier s = interior s
· 使用定理 `intrinsicInterior.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [
inst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 
: Topologica…
-/
theorem intrinsicClosure_sdiff_intrinsicFrontier (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
  (image_sdiff Subtype.coe_injective _ _).symm.trans <| by
    rw [closure_sdiff_frontier, intrinsicInterior]

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicFrontier := intrinsicClosure_sdiff_intrinsicFrontier

@[simp]
/-
**intrinsicClosure_sdiff_intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_sdiff_intrinsicInterior (s : Set P) : intrinsicClosure 𝕜 
s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem intrinsicClosure_sdiff_intrinsicInterior (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  (image_sdiff Subtype.coe_injective _ _).symm

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicInterior := intrinsicClosure_sdiff_intrinsicInterior

@[simp]
/-
**intrinsicInterior_union_intrinsicFrontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_union_intrinsicFrontier (s : Set P) : intrinsicInterior 
𝕜 s union intrinsicFrontier 𝕜 s = intrinsicClosure 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_interior_union_frontier`：closure_eq_interior_union_frontier (
s : Set X) : closure s = interior s union frontier s
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicInterior_union_intrinsicFrontier (s : Set P) :
    intrinsicInterior 𝕜 s ∪ intrinsicFrontier 𝕜 s = intrinsicClosure 𝕜 s := by
  simp [intrinsicClosure, intrinsicInterior, intrinsicFrontier, closure_eq_interior_union_frontier,
    image_union]

@[simp]
/-
**intrinsicFrontier_union_intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicFrontier_union_intrinsicInterior (s : Set P) : intrinsicFrontier 
𝕜 s union intrinsicInterior 𝕜 s = intrinsicClosure 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `intrinsicInterior_union_intrinsicFrontier`：intrinsicInterior_union_intri
nsicFrontier (s : Set P) : intrinsicInterior 𝕜 s union intrinsicFrontier 𝕜 s = i
ntrinsicClosure 𝕜 s
-/
theorem intrinsicFrontier_union_intrinsicInterior (s : Set P) :
    intrinsicFrontier 𝕜 s ∪ intrinsicInterior 𝕜 s = intrinsicClosure 𝕜 s := by
  rw [union_comm, intrinsicInterior_union_intrinsicFrontier]
/-
**isClosed_intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_intrinsicClosure (hs : IsClosed (affineSpan 𝕜 s : Set P)) : IsClo
sed (intrinsicClosure 𝕜 s)
参数：hs : IsClosed (affineSpan 𝕜 s : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_intrinsicClosure (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicClosure 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure
/-
**isClosed_intrinsicFrontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_intrinsicFrontier (hs : IsClosed (affineSpan 𝕜 s : Set P)) : IsCl
osed (intrinsicFrontier 𝕜 s)
参数：hs : IsClosed (affineSpan 𝕜 s : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `isClosed_frontier`：isClosed_frontier : IsClosed (frontier s)
-/
theorem isClosed_intrinsicFrontier (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicFrontier 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier

@[simp]
/-
**affineSpan_intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_intrinsicClosure (s : Set P) : affineSpan 𝕜 (intrinsicClosure 𝕜
 s) = affineSpan 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
· 使用定理 `intrinsicClosure_subset_affineSpan`：intrinsicClosure_subset_affineSpan :
 intrinsicClosure 𝕜 s subseteq affineSpan 𝕜 s
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `subset_intrinsicClosure`：subset_intrinsicClosure : s subseteq intrinsicC
losure 𝕜 s
-/
theorem affineSpan_intrinsicClosure (s : Set P) :
    affineSpan 𝕜 (intrinsicClosure 𝕜 s) = affineSpan 𝕜 s :=
  (affineSpan_le.2 intrinsicClosure_subset_affineSpan).antisymm <|
    affineSpan_mono _ subset_intrinsicClosure
/-
**IsClosed.intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 : TopologicalSpace P] [ins
t_4 : AddTorsor V P] {s : Set P},   IsClosed (Subtype.val ⁻¹' s) → intrinsicClos
ure 𝕜 s = s
参数：Subtype.val ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicClosure.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [i
nst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 :
 Topologica…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
protected theorem IsClosed.intrinsicClosure (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset

@[simp]
/-
**intrinsicClosure_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_idem (s : Set P) : intrinsicClosure 𝕜 (intrinsicClosure 𝕜
 s) = intrinsicClosure 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.intrinsicClosure`：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_5
} [inst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst
_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicClosure.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [i
nst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 :
 Topologica…
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `affineSpan_intrinsicClosure`：affineSpan_intrinsicClosure (s : Set P) : a
ffineSpan 𝕜 (intrinsicClosure 𝕜 s) = affineSpan 𝕜 s
-/
theorem intrinsicClosure_idem (s : Set P) :
    intrinsicClosure 𝕜 (intrinsicClosure 𝕜 s) = intrinsicClosure 𝕜 s := by
  refine IsClosed.intrinsicClosure ?_
  set t := affineSpan 𝕜 (intrinsicClosure 𝕜 s) with ht
  clear_value t
  obtain rfl := ht.trans (affineSpan_intrinsicClosure _)
  rw [intrinsicClosure, preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_closure
/-
**intrinsicClosure_eq_closure_inter_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_eq_closure_inter_affineSpan (s : Set P) : intrinsicClosur
e 𝕜 s = closure s inter affineSpan 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicClosure.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [i
nst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 :
 Topologica…
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
-/
theorem intrinsicClosure_eq_closure_inter_affineSpan (s : Set P) :
    intrinsicClosure 𝕜 s = closure s ∩ affineSpan 𝕜 s := by
  have h : Topology.IsInducing ((↑) : affineSpan 𝕜 s → P) := .subtypeVal
  rw [intrinsicClosure, h.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range,
    Set.image_preimage_eq_of_subset ?_, Subtype.range_coe]
  rw [Subtype.range_coe]
  apply subset_affineSpan
/-
**intrinsicInterior_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_prod_eq [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace 
Q] [AddTorsor W Q] (s : Set P) (t : Set Q) : intrinsicInterior 𝕜 (s ×ˢ t) = intr
insicInterior 𝕜 s ×ˢ intrinsicInterior 𝕜 t
参数：s : Set P；t : Set Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSpan_prod_eq`：∀ {k : Type u_1} {V : Type u_2} {W : Type u_3} {P : 
Type u_4} {Q : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V]   [inst_2 : _
root_.Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_interior`：preimage_interior (h : X ≃ₜ Y) (s : Set Y)
 : h ⁻¹' interior s = interior (h ⁻¹' s)
· 使用定理 `interior_prod_eq`：interior_prod_eq (s : Set X) (t : Set Y) : interior (s
 ×ˢ t) = interior s ×ˢ interior t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Set.prod_image_image_eq`：prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
-/
theorem intrinsicInterior_prod_eq [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q]
    [AddTorsor W Q] (s : Set P) (t : Set Q) :
    intrinsicInterior 𝕜 (s ×ˢ t) = intrinsicInterior 𝕜 s ×ˢ intrinsicInterior 𝕜 t := by
  let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
    (Homeomorph.setCongr (by simp [affineSpan_prod_eq])).trans (Homeomorph.Set.prod _ _)
  have : Subtype.val ∘ e.symm = fun p ↦ (p.1, p.2) := rfl
  have h : ((↑) ⁻¹' (s ×ˢ t) : Set _) = e ⁻¹' (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := rfl
  simp_rw [intrinsicInterior, h, ← e.preimage_interior, interior_prod_eq, ← e.image_symm,
    ← image_comp, prod_image_image_eq, this]

section ImageOfHomeomorphAffineSpan

variable [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q] [AddTorsor W Q]
  {f : P → Q} {s : Set P}

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` agrees with a homeomorphism between the affine spans of `s` and `f '' s`, then pulling
`f '' s` back to the affine span of `s` recovers `s` itself. -/
/-
**preimage_image_eq_of_homeomorph_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` agrees with a homeomorphism between the affine spans of `s` and `f '' s`,
 then pulling
`f '' s` back to the affine span of `s` recovers `s` itself.
-/
private theorem preimage_image_eq_of_homeomorph_affineSpan
    (e : affineSpan 𝕜 s → affineSpan 𝕜 (f '' s)) (he_homeo : IsHomeomorph e)
    (he : ∀ x, (e x : Q) = f x) :
    (f ∘ (↑)) ⁻¹' (f '' s) = ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) := by
  ext x
  refine ⟨fun ⟨_, hy, hfy⟩ ↦ ?_ , fun hx ↦ ⟨_, hx, rfl⟩⟩
  change (x : P) ∈ s
  rwa [exists_eq_subtype_mk_iff.mp ⟨subset_affineSpan 𝕜 s hy, he_homeo.injective <| Subtype.ext <|
      by simpa [he] using hfy.symm⟩]

variable (e : [Nonempty s] → affineSpan 𝕜 s → affineSpan 𝕜 (f '' s))
  (he_homeo : [Nonempty s] → IsHomeomorph e) (he : [Nonempty s] → ∀ x, e x = f x)

include e he_homeo he

/-- Naturality of intrinsic interior under a map whose induced map on affine spans is a
homeomorphism. It is introduced here to share the proof of the affine equivalence and affine
isometry versions below. -/
/-
**intrinsicInterior_image_of_homeomorph_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturality of intrinsic interior under a map whose induced map on affine spans i
s a
homeomorphism. It is introduced here to share the proof of the affine equivalenc
e and affine
isometry versions below.
-/
private theorem intrinsicInterior_image_of_homeomorph_affineSpan :
    intrinsicInterior 𝕜 (f '' s) = f '' intrinsicInterior 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicInterior, ← image_interior_preimage_comp e he_homeo,
      (funext he : (↑) ∘ e = f ∘ (↑)),
      preimage_image_eq_of_homeomorph_affineSpan e he_homeo he, image_comp]; rfl

/-- Naturality of intrinsic frontier under a map whose induced map on affine spans is a
homeomorphism. It is introduced here to share the proof of the affine equivalence and affine
isometry versions below. -/
/-
**intrinsicFrontier_image_of_homeomorph_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturality of intrinsic frontier under a map whose induced map on affine spans i
s a
homeomorphism. It is introduced here to share the proof of the affine equivalenc
e and affine
isometry versions below.
-/
private theorem intrinsicFrontier_image_of_homeomorph_affineSpan :
    intrinsicFrontier 𝕜 (f '' s) = f '' intrinsicFrontier 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicFrontier, ← image_frontier_preimage_comp e he_homeo,
      (funext he : (↑) ∘ e = f ∘ (↑)),
      preimage_image_eq_of_homeomorph_affineSpan e he_homeo he, image_comp]; rfl

/-- Naturality of intrinsic closure under a map whose induced map on affine spans is a
homeomorphism. It is introduced here to share the proof of the affine equivalence and affine
isometry versions below. -/
/-
**intrinsicClosure_image_of_homeomorph_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturality of intrinsic closure under a map whose induced map on affine spans is
 a
homeomorphism. It is introduced here to share the proof of the affine equivalenc
e and affine
isometry versions below.
-/
private theorem intrinsicClosure_image_of_homeomorph_affineSpan :
    intrinsicClosure 𝕜 (f '' s) = f '' intrinsicClosure 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicClosure, ← image_closure_preimage_comp e he_homeo,
      (funext he : (↑) ∘ e = f ∘ (↑)),
      preimage_image_eq_of_homeomorph_affineSpan e he_homeo he, image_comp]; rfl

end ImageOfHomeomorphAffineSpan

end AddTorsor

namespace ContinuousAffineEquiv

variable [Ring 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W]
  [TopologicalSpace P] [TopologicalSpace Q] [AddTorsor V P] [AddTorsor W Q]

@[simp]
/-
**ContinuousAffineEquiv.intrinsicInterior_image** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：intrinsicInterior_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicInterior 𝕜 
(φ '' s) = φ '' intrinsicInterior 𝕜 s
参数：φ : P ≃ᴬ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicInterior_image_of_
homeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type 
u_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_
.Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicInterior_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    (φ.affineSubspaceMap (affineSpan 𝕜 s)).trans <| ofEq (map_span φ.toAffineMap s)
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/-
**ContinuousAffineEquiv.intrinsicFrontier_image** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：intrinsicFrontier_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicFrontier 𝕜 
(φ '' s) = φ '' intrinsicFrontier 𝕜 s
参数：φ : P ≃ᴬ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicFrontier_image_of_
homeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type 
u_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_
.Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicFrontier_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    (φ.affineSubspaceMap (affineSpan 𝕜 s)).trans <| ofEq (map_span φ.toAffineMap s)
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/-
**ContinuousAffineEquiv.intrinsicClosure_image** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAffineEquiv`。
形式化陈述：intrinsicClosure_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicClosure 𝕜 (φ
 '' s) = φ '' intrinsicClosure 𝕜 s
参数：φ : P ≃ᴬ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicClosure_image_of_h
omeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type u
_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_.
Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicClosure_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    (φ.affineSubspaceMap (affineSpan 𝕜 s)).trans <| ofEq (map_span φ.toAffineMap s)
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

end ContinuousAffineEquiv

namespace AffineIsometry

variable [NormedField 𝕜] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [NormedSpace 𝕜 V]
  [NormedSpace 𝕜 W] [MetricSpace P] [PseudoMetricSpace Q] [NormedAddTorsor V P]
  [NormedAddTorsor W Q]

@[simp]
/-
**AffineIsometry.intrinsicInterior_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ry`。
形式化陈述：intrinsicInterior_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) : intrinsicInterior 
𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s
参数：φ : P ->ᵃⁱ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicInterior_image_of_
homeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type 
u_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_
.Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicInterior_image (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    ((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans <| ofEq <|
      (map_span φ.toAffineMap s).trans <| congrArg _ <| congrArg (· '' s) φ.coe_toAffineMap
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/-
**AffineIsometry.intrinsicFrontier_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ry`。
形式化陈述：intrinsicFrontier_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) : intrinsicFrontier 
𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s
参数：φ : P ->ᵃⁱ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicFrontier_image_of_
homeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type 
u_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_
.Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicFrontier_image (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    ((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans <| ofEq <|
      (map_span φ.toAffineMap s).trans <| congrArg _ <| congrArg (· '' s) φ.coe_toAffineMap
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/-
**AffineIsometry.intrinsicClosure_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometr
y`。
形式化陈述：intrinsicClosure_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) : intrinsicClosure 𝕜 
(φ '' s) = φ '' intrinsicClosure 𝕜 s
参数：φ : P ->ᵃⁱ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.intrinsicClosure_image_of_h
omeomorph_affineSpan`：∀ {𝕜 : Type u_1} {V : Type u_2} {W : Type u_3} {Q : Type u
_4} {P : Type u_5} [inst : Ring 𝕜] [inst_1 : AddCommGroup V]   [inst_2 : _root_.
Mo…
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem intrinsicClosure_image (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  let e : [Nonempty s] → (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
    ((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans <| ofEq <|
      (map_span φ.toAffineMap s).trans <| congrArg _ <| congrArg (· '' s) φ.coe_toAffineMap
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[deprecated intrinsicInterior_image (since := "2026-05-08")]
alias image_intrinsicInterior := intrinsicInterior_image

@[deprecated intrinsicFrontier_image (since := "2026-05-08")]
alias image_intrinsicFrontier := intrinsicFrontier_image

@[deprecated intrinsicClosure_image (since := "2026-05-08")]
alias image_intrinsicClosure := intrinsicClosure_image

end AffineIsometry

namespace AffineEquiv

variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [MetricSpace P] [NormedAddTorsor V P]
  [MetricSpace Q] [NormedAddTorsor W Q]

@[simp]
/-
**AffineEquiv.intrinsicInterior_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：intrinsicInterior_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) : intrinsicInterior 𝕜 
(φ '' s) = φ '' intrinsicInterior 𝕜 s
参数：φ : P ≃ᵃ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.intrinsicInterior_image`：intrinsicInterior_image (
φ : P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInteri
or 𝕜 s
-/
theorem intrinsicInterior_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicInterior_image s

@[simp]
/-
**AffineEquiv.intrinsicFrontier_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：intrinsicFrontier_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) : intrinsicFrontier 𝕜 
(φ '' s) = φ '' intrinsicFrontier 𝕜 s
参数：φ : P ≃ᵃ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.intrinsicFrontier_image`：intrinsicFrontier_image (
φ : P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFronti
er 𝕜 s
-/
theorem intrinsicFrontier_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicFrontier_image s

@[simp]
/-
**AffineEquiv.intrinsicClosure_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：intrinsicClosure_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) : intrinsicClosure 𝕜 (φ
 '' s) = φ '' intrinsicClosure 𝕜 s
参数：φ : P ≃ᵃ[𝕜] Q；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.intrinsicClosure_image`：intrinsicClosure_image (φ 
: P ≃ᴬ[𝕜] Q) (s : Set P) : intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜
 s
-/
theorem intrinsicClosure_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicClosure_image s

end AffineEquiv

section NormedAddTorsor

variable (𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [MetricSpace P] [NormedAddTorsor V P] (s : Set P)

@[simp]
/-
**intrinsicClosure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicClosure_eq_closure : intrinsicClosure 𝕜 s = closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `AffineSubspace.closed_of_finiteDimensional`：AffineSubspace.closed_of_fin
iteDimensional {P : Type*} [MetricSpace P] [NormedAddTorsor E P] (s : AffineSubs
pace 𝕜 P) [FiniteDimensional 𝕜 s…
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem intrinsicClosure_eq_closure : intrinsicClosure 𝕜 s = closure s := by
  ext x
  simp only [mem_closure_iff, mem_intrinsicClosure]
  refine ⟨?_, fun h => ⟨⟨x, _⟩, ?_, Subtype.coe_mk _ ?_⟩⟩
  · rintro ⟨x, h, rfl⟩ t ht hx
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.isOpen_preimage t ht) hx
    exact ⟨z, hz₁, hz₂⟩
  · rintro _ ⟨t, ht, rfl⟩ hx
    obtain ⟨y, hyt, hys⟩ := h _ ht hx
    exact ⟨⟨_, subset_affineSpan 𝕜 s hys⟩, hyt, hys⟩
  · by_contra hc
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affineSpan 𝕜 s).closed_of_finiteDimensional.isOpen_compl hc
    exact hz₁ (subset_affineSpan 𝕜 s hz₂)

variable {𝕜}

@[simp]
/-
**closure_sdiff_intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_sdiff_intrinsicInterior (s : Set P) : closure s \ intrinsicInterio
r 𝕜 s = intrinsicFrontier 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intrinsicClosure_sdiff_intrinsicInterior`：intrinsicClosure_sdiff_intrins
icInterior (s : Set P) : intrinsicClosure 𝕜 s \ intrinsicInterior 𝕜 s = intrinsi
cFrontier 𝕜 s
· 使用定理 `intrinsicClosure_eq_closure`：intrinsicClosure_eq_closure : intrinsicClos
ure 𝕜 s = closure s
-/
theorem closure_sdiff_intrinsicInterior (s : Set P) :
    closure s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicInterior s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicInterior := closure_sdiff_intrinsicInterior

@[simp]
/-
**closure_sdiff_intrinsicFrontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_sdiff_intrinsicFrontier (s : Set P) : closure s \ intrinsicFrontie
r 𝕜 s = intrinsicInterior 𝕜 s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intrinsicClosure_sdiff_intrinsicFrontier`：intrinsicClosure_sdiff_intrins
icFrontier (s : Set P) : intrinsicClosure 𝕜 s \ intrinsicFrontier 𝕜 s = intrinsi
cInterior 𝕜 s
· 使用定理 `intrinsicClosure_eq_closure`：intrinsicClosure_eq_closure : intrinsicClos
ure 𝕜 s = closure s
-/
theorem closure_sdiff_intrinsicFrontier (s : Set P) :
    closure s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicFrontier s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicFrontier := closure_sdiff_intrinsicFrontier

end NormedAddTorsor

section Convex

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul 𝕜 V] {s : Set V}

/-
**Convex.intrinsicClosure** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[inst_2 : AddCommGroup V]   [inst_3 : _root_.Module 𝕜 V] [inst_4 : TopologicalSp
ace V] [IsTopologicalAddGroup V] [ContinuousConstSMul 𝕜 V]   {s : Set V}, Convex
 𝕜 s → Convex 𝕜 (intrinsicClosure 𝕜 s)
参数：intrinsicClosure 𝕜 s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicClosure_eq_closure_inter_affineSpan`：intrinsicClosure_eq_closur
e_inter_affineSpan (s : Set P) : intrinsicClosure 𝕜 s = closure s inter affineSp
an 𝕜 s
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `AffineSubspace.convex`：AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : 
Convex 𝕜 (Q : Set E)
-/
protected theorem Convex.intrinsicClosure (hs : Convex 𝕜 s) : Convex 𝕜 (intrinsicClosure 𝕜 s) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact hs.closure.inter (affineSpan 𝕜 s).convex

end Convex

/-
**aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (φ : α ≃ₜ β)
    (s : Set β) : (interior s).Nonempty ↔ (interior (φ ⁻¹' s)).Nonempty := by
  rw [← φ.image_symm, ← φ.symm.image_interior, image_nonempty]

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V}

/-- The intrinsic interior of a nonempty convex set is nonempty. -/
/-
**Set.Nonempty.intrinsicInterior** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {V : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] 
[FiniteDimensional ℝ V] {s : Set V},   Convex ℝ s → s.Nonempty → (intrinsicInter
ior ℝ s).Nonempty
参数：intrinsicInterior ℝ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intrinsicInterior.eq_1`：∀ (𝕜 : Type u_1) {V : Type u_2} {P : Type u_5} [
inst : Ring 𝕜] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3 
: Topologica…
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `_private.Mathlib.Analysis.Convex.Intrinsic.0.aux`：∀ {α : Type u_6} {β : 
Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] (φ : α ≃ₜ β)
 (s : Set β),   (interior s).Nonempty …
· 使用定理 `Convex.interior_nonempty_iff_affineSpan_eq_top`：Convex.interior_nonempty
_iff_affineSpan_eq_top [FiniteDimensional Real V] {s : Set V} (hs : Convex Real 
s) : (interior s).Nonempty ↔ affineS…
· 使用定理 `Convex.affine_preimage`：Convex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set
 F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `AffineIsometryEquiv.coe_toHomeomorph`：coe_toHomeomorph : ⇑e.toHomeomorph
 = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIsometryEquiv.coe_toAffineEquiv`：coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P
₂) : ⇑e.toAffineEquiv = e
· 使用定理 `AffineSubspace.comap_span`：comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : (
affineSpan k s).comap (f : P₁ ->ᵃ[k] P₂) = affineSpan k (f ⁻¹' s)
· 使用定理 `affineSpan_coe_preimage_eq_top`：affineSpan_coe_preimage_eq_top (A : Set 
P) [Nonempty A] : affineSpan k (((↑) : affineSpan k A -> P) ⁻¹' A) = ⊤
· 使用定理 `AffineSubspace.comap_top`：comap_top {f : P₁ ->ᵃ[k] P₂} : (⊤ : AffineSubs
pace k P₂).comap f = ⊤

--- 原说明 ---
The intrinsic interior of a nonempty convex set is nonempty.
-/
protected theorem Set.Nonempty.intrinsicInterior (hscv : Convex ℝ s) (hsne : s.Nonempty) :
    (intrinsicInterior ℝ s).Nonempty := by
  have := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan ℝ s := ⟨p, subset_affineSpan _ _ hp⟩
  rw [intrinsicInterior, image_nonempty,
    aux (AffineIsometryEquiv.constVSub ℝ p').symm.toHomeomorph,
    Convex.interior_nonempty_iff_affineSpan_eq_top, AffineIsometryEquiv.coe_toHomeomorph, ←
    AffineIsometryEquiv.coe_toAffineEquiv, ← comap_span, affineSpan_coe_preimage_eq_top, comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ p').symm.toAffineEquiv.toAffineMap)
/-
**intrinsicInterior_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intrinsicInterior_nonempty (hs : Convex Real s) : (intrinsicInterior Real 
s).Nonempty ↔ s.Nonempty
参数：hs : Convex Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `intrinsicInterior_empty`：intrinsicInterior_empty : intrinsicInterior 𝕜 (
∅ : Set P) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.intrinsicInterior`：∀ {V : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V},   Convex 
ℝ s → s.Nonempty → (…
-/
theorem intrinsicInterior_nonempty (hs : Convex ℝ s) :
    (intrinsicInterior ℝ s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicInterior_empty,
    Set.Nonempty.intrinsicInterior hs⟩
