/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.FieldSimp

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points.

## Main definitions

* `affineSegment R x y`: The segment of points weakly between `x` and `y`.
* `Wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `Sbtw R x y z`: The point `y` is strictly between `x` and `z`.

-/

@[expose] public section


variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap Module

section OrderedRing

set_option backward.isDefEq.respectTransparency false in
/-- The segment of points weakly between `x` and `y`. When convexity is refactored to support
abstract affine combination spaces, this will no longer need to be a separate definition from
`segment`. However, lemmas involving `+ᵥ` or `-ᵥ` will still be relevant after such a
refactoring, as distinct from versions involving `+` or `-` in a module. -/
/-
**affineSegment** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：affineSegment [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [Add
Torsor V P] (x y : P)
参数：x y : P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The segment of points weakly between `x` and `y`. When convexity is refactored t
o support
abstract affine combination spaces, this will no longer need to be a separate de
finition from
`segment`. However, lemmas involving `+ᵥ` or `-ᵥ` will still be relevant after s
uch a
refactoring, as distinct from versions involving `+` or `-` in a module.
-/
def affineSegment [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V]
    [AddTorsor V P] (x y : P) :=
  lineMap x y '' Set.Icc (0 : R) 1

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']
/-
**affineSegment_subset_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSegment_subset_affineSpan (x y : P) : affineSegment R x y subseteq l
ine[R, x, y]
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `AffineMap.lineMap_mem_affineSpan_pair`：AffineMap.lineMap_mem_affineSpan_
pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂]
-/
lemma affineSegment_subset_affineSpan (x y : P) : affineSegment R x y ⊆ line[R, x, y] := by
  rw [affineSegment, Set.subset_def]
  rintro p ⟨r, -, rfl⟩
  exact lineMap_mem_affineSpan_pair _ _ _

variable {R} in
@[simp]
/-
**affineSegment_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f '' affineSegment R x y
 = affineSegment R (f x) (f y)
参数：f : P ->ᵃ[R] P'；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.comp_lineMap`：comp_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) : f
.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁)
-/
theorem affineSegment_image (f : P →ᵃ[R] P') (x y : P) :
    f '' affineSegment R x y = affineSegment R (f x) (f y) := by
  rw [affineSegment, affineSegment, Set.image_image, ← comp_lineMap]
  rfl

@[simp]
/-
**affineSegment_const_vadd_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_const_vadd_image (x y : P) (v : V) : (v +ᵥ ·) '' affineSegme
nt R x y = affineSegment R (v +ᵥ x) (v +ᵥ y)
参数：x y : P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
-/
theorem affineSegment_const_vadd_image (x y : P) (v : V) :
    (v +ᵥ ·) '' affineSegment R x y = affineSegment R (v +ᵥ x) (v +ᵥ y) :=
  affineSegment_image (AffineEquiv.constVAdd R P v : P →ᵃ[R] P) x y

@[simp]
/-
**affineSegment_vadd_const_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_vadd_const_image (x y : V) (p : P) : (· +ᵥ p) '' affineSegme
nt R x y = affineSegment R (x +ᵥ p) (y +ᵥ p)
参数：x y : V；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
-/
theorem affineSegment_vadd_const_image (x y : V) (p : P) :
    (· +ᵥ p) '' affineSegment R x y = affineSegment R (x +ᵥ p) (y +ᵥ p) :=
  affineSegment_image (AffineEquiv.vaddConst R p : V →ᵃ[R] P) x y

@[simp]
/-
**affineSegment_const_vsub_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_const_vsub_image (x y p : P) : (p -ᵥ ·) '' affineSegment R x
 y = affineSegment R (p -ᵥ x) (p -ᵥ y)
参数：x y p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
-/
theorem affineSegment_const_vsub_image (x y p : P) :
    (p -ᵥ ·) '' affineSegment R x y = affineSegment R (p -ᵥ x) (p -ᵥ y) :=
  affineSegment_image (AffineEquiv.constVSub R p : P →ᵃ[R] V) x y

@[simp]
/-
**affineSegment_vsub_const_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_vsub_const_image (x y p : P) : (· -ᵥ p) '' affineSegment R x
 y = affineSegment R (x -ᵥ p) (y -ᵥ p)
参数：x y p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
-/
theorem affineSegment_vsub_const_image (x y p : P) :
    (· -ᵥ p) '' affineSegment R x y = affineSegment R (x -ᵥ p) (y -ᵥ p) :=
  affineSegment_image ((AffineEquiv.vaddConst R p).symm : P →ᵃ[R] V) x y

variable {R}

@[simp]
/-
**mem_const_vadd_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_const_vadd_affineSegment {x y z : P} (v : V) : v +ᵥ z in affineSegment
 R (v +ᵥ x) (v +ᵥ y) ↔ z in affineSegment R x y
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_const_vadd_image`：affineSegment_const_vadd_image (x y : P)
 (v : V) : (v +ᵥ ·) '' affineSegment R x y = affineSegment R (v +ᵥ x) (v +ᵥ y)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `AddAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : AddGroup α]
 [inst_1 : AddAction α β] (g : α), Function.Injective fun x => g +ᵥ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_const_vadd_affineSegment {x y z : P} (v : V) :
    v +ᵥ z ∈ affineSegment R (v +ᵥ x) (v +ᵥ y) ↔ z ∈ affineSegment R x y := by
  rw [← affineSegment_const_vadd_image, (AddAction.injective v).mem_set_image]

@[simp]
/-
**mem_vadd_const_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_vadd_const_affineSegment {x y z : V} (p : P) : z +ᵥ p in affineSegment
 R (x +ᵥ p) (y +ᵥ p) ↔ z in affineSegment R x y
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_vadd_const_image`：affineSegment_vadd_const_image (x y : V)
 (p : P) : (· +ᵥ p) '' affineSegment R x y = affineSegment R (x +ᵥ p) (y +ᵥ p)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `vadd_right_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p : P), Function.Injective fun x => x +ᵥ p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vadd_const_affineSegment {x y z : V} (p : P) :
    z +ᵥ p ∈ affineSegment R (x +ᵥ p) (y +ᵥ p) ↔ z ∈ affineSegment R x y := by
  rw [← affineSegment_vadd_const_image, (vadd_right_injective p).mem_set_image]

@[simp]
/-
**mem_const_vsub_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_const_vsub_affineSegment {x y z : P} (p : P) : p -ᵥ z in affineSegment
 R (p -ᵥ x) (p -ᵥ y) ↔ z in affineSegment R x y
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_const_vsub_image`：affineSegment_const_vsub_image (x y p : 
P) : (p -ᵥ ·) '' affineSegment R x y = affineSegment R (p -ᵥ x) (p -ᵥ y)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `vsub_right_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p : P), Function.Injective fun x => p -ᵥ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_const_vsub_affineSegment {x y z : P} (p : P) :
    p -ᵥ z ∈ affineSegment R (p -ᵥ x) (p -ᵥ y) ↔ z ∈ affineSegment R x y := by
  rw [← affineSegment_const_vsub_image, (vsub_right_injective p).mem_set_image]

@[simp]
/-
**mem_vsub_const_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_vsub_const_affineSegment {x y z : P} (p : P) : z -ᵥ p in affineSegment
 R (x -ᵥ p) (y -ᵥ p) ↔ z in affineSegment R x y
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_vsub_const_image`：affineSegment_vsub_const_image (x y p : 
P) : (· -ᵥ p) '' affineSegment R x y = affineSegment R (x -ᵥ p) (y -ᵥ p)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vsub_const_affineSegment {x y z : P} (p : P) :
    z -ᵥ p ∈ affineSegment R (x -ᵥ p) (y -ᵥ p) ↔ z ∈ affineSegment R x y := by
  rw [← affineSegment_vsub_const_image, (vsub_left_injective p).mem_set_image]

variable (R)

section OrderedRing
variable [IsOrderedRing R]

/-
**affineSegment_eq_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_eq_segment (x y : V) : affineSegment R x y = segment R x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
-/
theorem affineSegment_eq_segment (x y : V) : affineSegment R x y = segment R x y := by
  rw [segment_eq_image_lineMap, affineSegment]
/-
**affineSegment_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_comm (x y : P) : affineSegment R x y = affineSegment R y x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sub_mem_Icc_iff_right`：sub_mem_Icc_iff_right : a - b in Set.Icc c d 
↔ b in Set.Icc (a - d) (a - c)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
-/
theorem affineSegment_comm (x y : P) : affineSegment R x y = affineSegment R y x := by
  refine Set.ext fun z => ?_
  constructor <;>
    · rintro ⟨t, ht, hxy⟩
      refine ⟨1 - t, ?_, ?_⟩
      · rwa [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]
      · rwa [lineMap_apply_one_sub]
/-
**left_mem_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_mem_affineSegment (x y : P) : x in affineSegment R x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
-/
theorem left_mem_affineSegment (x y : P) : x ∈ affineSegment R x y :=
  ⟨0, Set.left_mem_Icc.2 zero_le_one, lineMap_apply_zero _ _⟩
/-
**right_mem_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_mem_affineSegment (x y : P) : y in affineSegment R x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
-/
theorem right_mem_affineSegment (x y : P) : y ∈ affineSegment R x y :=
  ⟨1, Set.right_mem_Icc.2 zero_le_one, lineMap_apply_one _ _⟩

@[simp]
/-
**affineSegment_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment_same (x : P) : affineSegment R x x = {x}
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineSegment_same (x : P) : affineSegment R x x = {x} := by
  simp_rw [affineSegment, lineMap_same, AffineMap.coe_const, Function.const,
    (Set.nonempty_Icc.mpr zero_le_one).image_const]

end OrderedRing

/-- The point `y` is weakly between `x` and `z`. -/
/-
**Wbtw** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Wbtw (x y z : P) : Prop
参数：x y z : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point `y` is weakly between `x` and `z`.
-/
def Wbtw (x y z : P) : Prop :=
  y ∈ affineSegment R x z

/-- The point `y` is strictly between `x` and `z`. -/
/-
**Sbtw** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Sbtw (x y z : P) : Prop
参数：x y z : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point `y` is strictly between `x` and `z`.
-/
def Sbtw (x y z : P) : Prop :=
  Wbtw R x y z ∧ y ≠ x ∧ y ≠ z

variable {R}

section OrderedRing

variable [IsOrderedRing R]

/-
**mem_segment_iff_wbtw** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_segment_iff_wbtw {x y z : V} : y in segment R x z ↔ Wbtw R x y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `affineSegment_eq_segment`：affineSegment_eq_segment (x y : V) : affineSeg
ment R x y = segment R x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_segment_iff_wbtw {x y z : V} : y ∈ segment R x z ↔ Wbtw R x y z := by
  rw [Wbtw, affineSegment_eq_segment]

alias ⟨_, Wbtw.mem_segment⟩ := mem_segment_iff_wbtw
/-
**Convex.mem_of_wbtw** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.mem_of_wbtw {p₀ p₁ p₂ : V} {s : Set V} (hs : Convex R s) (h₀₁₂ : Wb
tw R p₀ p₁ p₂) (h₀ : p₀ in s) (h₂ : p₂ in s) : p₁ in s
参数：hs : Convex R s；h₀₁₂ : Wbtw R p₀ p₁ p₂；h₀ : p₀ in s；h₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `Wbtw.mem_segment`：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_
1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [Is
Ordere…
-/
lemma Convex.mem_of_wbtw {p₀ p₁ p₂ : V} {s : Set V} (hs : Convex R s) (h₀₁₂ : Wbtw R p₀ p₁ p₂)
    (h₀ : p₀ ∈ s) (h₂ : p₂ ∈ s) : p₁ ∈ s := hs.segment_subset h₀ h₂ h₀₁₂.mem_segment
/-
**wbtw_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `affineSegment_comm`：affineSegment_comm (x y : P) : affineSegment R x y =
 affineSegment R y x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x := by
  rw [Wbtw, Wbtw, affineSegment_comm]

alias ⟨Wbtw.symm, _⟩ := wbtw_comm
/-
**sbtw_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_right_comm`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x := by
  rw [Sbtw, Sbtw, wbtw_comm, ← and_assoc, ← and_assoc, and_right_comm]

alias ⟨Sbtw.symm, _⟩ := sbtw_comm

end OrderedRing

/-
**AffineSubspace.mem_of_wbtw** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineSubspace.mem_of_wbtw {s : AffineSubspace R P} {x y z : P} (hxyz : Wb
tw R x y z) (hx : x in s) (hz : z in s) : y in s
参数：hxyz : Wbtw R x y z；hx : x in s；hz : z in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
-/
lemma AffineSubspace.mem_of_wbtw {s : AffineSubspace R P} {x y z : P} (hxyz : Wbtw R x y z)
    (hx : x ∈ s) (hz : z ∈ s) : y ∈ s := by obtain ⟨ε, -, rfl⟩ := hxyz; exact lineMap_mem _ hx hz
/-
**Wbtw.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P') : Wbtw R (f x) (
f y) (f z)
参数：h : Wbtw R x y z；f : P ->ᵃ[R] P'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P →ᵃ[R] P') : Wbtw R (f x) (f y) (f z) := by
  rw [Wbtw, ← affineSegment_image]
  exact Set.mem_image_of_mem _ h
/-
**Function.Injective.wbtw_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.wbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} (hf : Functi
on.Injective f) : Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Wbtw.map`：Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P') : Wb
tw R (f x) (f y) (f z)
-/
theorem Function.Injective.wbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_set_image] at h
/-
**Function.Injective.sbtw_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.sbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} (hf : Functi
on.Injective f) : Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.wbtw_map_iff`：Function.Injective.wbtw_map_iff {x y z 
: P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f) : Wbtw R (f x) (f y) (f z) ↔ 
Wbtw R x y z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Function.Injective.sbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, hf.wbtw_map_iff, hf.ne_iff]
/-
**Set.InjOn.wbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.InjOn.wbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R
 P} (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (hz : z in s) : Wbtw R (f x
) (f y) (f z) ↔ Wbtw R x y z
参数：hf : Set.InjOn f s；hx : x in s；hy : y in s；hz : z in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.mem_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} 
{f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → (f x ∈ f '' s₁ ↔ x ∈ s₁)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `affineSegment_subset_affineSpan`：affineSegment_subset_affineSpan (x y : 
P) : affineSegment R x y subseteq line[R, x, y]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
· 使用定理 `Set.pair_subset`：pair_subset (ha : a in s) (hb : b in s) : {a, b} subset
eq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_image`：affineSegment_image (f : P ->ᵃ[R] P') (x y : P) : f
 '' affineSegment R x y = affineSegment R (f x) (f y)
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Wbtw.map`：Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P ->ᵃ[R] P') : Wb
tw R (f x) (f y) (f z)
-/
lemma Set.InjOn.wbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} {s : AffineSubspace R P}
    (hf : Set.InjOn f s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rwa [Wbtw, ← affineSegment_image, hf.mem_image_iff
    ((affineSegment_subset_affineSpan R x z).trans (affineSpan_le.2 (Set.pair_subset hx hz))) hy]
    at h
/-
**Set.InjOn.sbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.InjOn.sbtw_map_iff {x y z : P} {f : P ->ᵃ[R] P'} {s : AffineSubspace R
 P} (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (hz : z in s) : Sbtw R (f x
) (f y) (f z) ↔ Sbtw R x y z
参数：hf : Set.InjOn f s；hx : x in s；hy : y in s；hz : z in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.InjOn.wbtw_map_iff`：Set.InjOn.wbtw_map_iff {x y z : P} {f : P ->ᵃ[R]
 P'} {s : AffineSubspace R P} (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (
hz : z in s)…
· 使用定理 `Set.InjOn.ne_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x ≠ f y ↔ x ≠ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.InjOn.sbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} {s : AffineSubspace R P}
    (hf : Set.InjOn f s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, hf.wbtw_map_iff hx hy hz, hf.ne_iff hy hx, hf.ne_iff hy hz]

@[simp]
/-
**AffineEquiv.wbtw_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.wbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') : Wbtw R (f x) (f y)
 (f z) ↔ Wbtw R x y z
参数：f : P ≃ᵃ[R] P'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
· 使用定理 `Function.Injective.wbtw_map_iff`：Function.Injective.wbtw_map_iff {x y z 
: P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f) : Wbtw R (f x) (f y) (f z) ↔ 
Wbtw R x y z
-/
theorem AffineEquiv.wbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.wbtw_map_iff

@[simp]
/-
**AffineEquiv.sbtw_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.sbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') : Sbtw R (f x) (f y)
 (f z) ↔ Sbtw R x y z
参数：f : P ≃ᵃ[R] P'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
· 使用定理 `Function.Injective.sbtw_map_iff`：Function.Injective.sbtw_map_iff {x y z 
: P} {f : P ->ᵃ[R] P'} (hf : Function.Injective f) : Sbtw R (f x) (f y) (f z) ↔ 
Sbtw R x y z
-/
theorem AffineEquiv.sbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  have : Function.Injective f.toAffineMap := f.injective
  -- `refine` or `exact` are very slow, `apply` is fast. Please check before golfing.
  apply this.sbtw_map_iff

@[simp]
/-
**wbtw_const_vadd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_const_vadd_iff {x y z : P} (v : V) : Wbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z
) ↔ Wbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_const_vadd_affineSegment`：mem_const_vadd_affineSegment {x y z : P} (
v : V) : v +ᵥ z in affineSegment R (v +ᵥ x) (v +ᵥ y) ↔ z in affineSegment R x y
-/
theorem wbtw_const_vadd_iff {x y z : P} (v : V) :
    Wbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vadd_affineSegment _

alias ⟨_, Wbtw.const_vadd⟩ := wbtw_const_vadd_iff

@[simp]
/-
**wbtw_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_const_add_iff {x y z : V} (v : V) : Wbtw R (v + x) (v + y) (v + z) ↔ 
Wbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_const_vadd_iff`：wbtw_const_vadd_iff {x y z : P} (v : V) : Wbtw R (v
 +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Wbtw R x y z
-/
theorem wbtw_const_add_iff {x y z : V} (v : V) :
    Wbtw R (v + x) (v + y) (v + z) ↔ Wbtw R x y z :=
  wbtw_const_vadd_iff v

alias ⟨_, Wbtw.const_add⟩ := wbtw_const_add_iff

@[simp]
/-
**wbtw_vadd_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_vadd_const_iff {x y z : V} (p : P) : Wbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p
) ↔ Wbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_vadd_const_affineSegment`：mem_vadd_const_affineSegment {x y z : V} (
p : P) : z +ᵥ p in affineSegment R (x +ᵥ p) (y +ᵥ p) ↔ z in affineSegment R x y
-/
theorem wbtw_vadd_const_iff {x y z : V} (p : P) :
    Wbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Wbtw R x y z :=
  mem_vadd_const_affineSegment _

alias ⟨_, Wbtw.vadd_const⟩ := wbtw_vadd_const_iff

@[simp]
/-
**wbtw_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_add_const_iff {x y z : V} (v : V) : Wbtw R (x + v) (y + v) (z + v) ↔ 
Wbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_vadd_const_iff`：wbtw_vadd_const_iff {x y z : V} (p : P) : Wbtw R (x
 +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Wbtw R x y z
-/
theorem wbtw_add_const_iff {x y z : V} (v : V) :
    Wbtw R (x + v) (y + v) (z + v) ↔ Wbtw R x y z :=
  wbtw_vadd_const_iff v

alias ⟨_, Wbtw.add_const⟩ := wbtw_add_const_iff

@[simp]
/-
**wbtw_const_vsub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_const_vsub_iff {x y z : P} (p : P) : Wbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z
) ↔ Wbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_const_vsub_affineSegment`：mem_const_vsub_affineSegment {x y z : P} (
p : P) : p -ᵥ z in affineSegment R (p -ᵥ x) (p -ᵥ y) ↔ z in affineSegment R x y
-/
theorem wbtw_const_vsub_iff {x y z : P} (p : P) :
    Wbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vsub_affineSegment _

alias ⟨_, Wbtw.const_vsub⟩ := wbtw_const_vsub_iff

@[simp]
/-
**wbtw_const_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_const_sub_iff {x y z : V} (v : V) : Wbtw R (v - x) (v - y) (v - z) ↔ 
Wbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_const_vsub_iff`：wbtw_const_vsub_iff {x y z : P} (p : P) : Wbtw R (p
 -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Wbtw R x y z
-/
theorem wbtw_const_sub_iff {x y z : V} (v : V) :
    Wbtw R (v - x) (v - y) (v - z) ↔ Wbtw R x y z :=
  wbtw_const_vsub_iff v

alias ⟨_, Wbtw.const_sub⟩ := wbtw_const_sub_iff

@[simp]
/-
**wbtw_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_neg_iff {x y z : V} : Wbtw R (-x) (-y) (-z) ↔ Wbtw R x y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wbtw_neg_iff {x y z : V} :
    Wbtw R (-x) (-y) (-z) ↔ Wbtw R x y z := by
  simp only [← zero_sub, wbtw_const_sub_iff]

alias ⟨_, Wbtw.neg⟩ := wbtw_neg_iff

@[simp]
/-
**wbtw_vsub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p
) ↔ Wbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_vsub_const_affineSegment`：mem_vsub_const_affineSegment {x y z : P} (
p : P) : z -ᵥ p in affineSegment R (x -ᵥ p) (y -ᵥ p) ↔ z in affineSegment R x y
-/
theorem wbtw_vsub_const_iff {x y z : P} (p : P) :
    Wbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z :=
  mem_vsub_const_affineSegment _

alias ⟨_, Wbtw.vsub_const⟩ := wbtw_vsub_const_iff

@[simp]
/-
**wbtw_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_sub_const_iff {x y z : V} (v : V) : Wbtw R (x - v) (y - v) (z - v) ↔ 
Wbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_vsub_const_iff`：wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x
 -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z
-/
theorem wbtw_sub_const_iff {x y z : V} (v : V) :
    Wbtw R (x - v) (y - v) (z - v) ↔ Wbtw R x y z :=
  wbtw_vsub_const_iff v

alias ⟨_, Wbtw.sub_const⟩ := wbtw_sub_const_iff

@[simp]
/-
**sbtw_const_vadd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_const_vadd_iff {x y z : P} (v : V) : Sbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z
) ↔ Sbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_const_vadd_iff`：wbtw_const_vadd_iff {x y z : P} (v : V) : Wbtw R (v
 +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Wbtw R x y z
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `AddAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : AddGroup α]
 [inst_1 : AddAction α β] (g : α), Function.Injective fun x => g +ᵥ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_const_vadd_iff {x y z : P} (v : V) :
    Sbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Sbtw R x y z := by
  rw [Sbtw, Sbtw, wbtw_const_vadd_iff, (AddAction.injective v).ne_iff,
    (AddAction.injective v).ne_iff]

alias ⟨_, Sbtw.const_vadd⟩ := sbtw_const_vadd_iff

@[simp]
/-
**sbtw_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_const_add_iff {x y z : V} (v : V) : Sbtw R (v + x) (v + y) (v + z) ↔ 
Sbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_const_vadd_iff`：sbtw_const_vadd_iff {x y z : P} (v : V) : Sbtw R (v
 +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Sbtw R x y z
-/
theorem sbtw_const_add_iff {x y z : V} (v : V) :
    Sbtw R (v + x) (v + y) (v + z) ↔ Sbtw R x y z :=
  sbtw_const_vadd_iff v

alias ⟨_, Sbtw.const_add⟩ := sbtw_const_add_iff

@[simp]
/-
**sbtw_vadd_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_vadd_const_iff {x y z : V} (p : P) : Sbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p
) ↔ Sbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_vadd_const_iff`：wbtw_vadd_const_iff {x y z : V} (p : P) : Wbtw R (x
 +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Wbtw R x y z
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `vadd_right_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p : P), Function.Injective fun x => x +ᵥ p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_vadd_const_iff {x y z : V} (p : P) :
    Sbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Sbtw R x y z := by
  rw [Sbtw, Sbtw, wbtw_vadd_const_iff, (vadd_right_injective p).ne_iff,
    (vadd_right_injective p).ne_iff]

alias ⟨_, Sbtw.vadd_const⟩ := sbtw_vadd_const_iff

@[simp]
/-
**sbtw_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_add_const_iff {x y z : V} (v : V) : Sbtw R (x + v) (y + v) (z + v) ↔ 
Sbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_vadd_const_iff`：sbtw_vadd_const_iff {x y z : V} (p : P) : Sbtw R (x
 +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Sbtw R x y z
-/
theorem sbtw_add_const_iff {x y z : V} (v : V) :
    Sbtw R (x + v) (y + v) (z + v) ↔ Sbtw R x y z :=
  sbtw_vadd_const_iff v

alias ⟨_, Sbtw.add_const⟩ := sbtw_add_const_iff

@[simp]
/-
**sbtw_const_vsub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_const_vsub_iff {x y z : P} (p : P) : Sbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z
) ↔ Sbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_const_vsub_iff`：wbtw_const_vsub_iff {x y z : P} (p : P) : Wbtw R (p
 -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Wbtw R x y z
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `vsub_right_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p : P), Function.Injective fun x => p -ᵥ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_const_vsub_iff {x y z : P} (p : P) :
    Sbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Sbtw R x y z := by
  rw [Sbtw, Sbtw, wbtw_const_vsub_iff, (vsub_right_injective p).ne_iff,
    (vsub_right_injective p).ne_iff]

alias ⟨_, Sbtw.const_vsub⟩ := sbtw_const_vsub_iff

@[simp]
/-
**sbtw_const_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_const_sub_iff {x y z : V} (v : V) : Sbtw R (v - x) (v - y) (v - z) ↔ 
Sbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_const_vsub_iff`：sbtw_const_vsub_iff {x y z : P} (p : P) : Sbtw R (p
 -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Sbtw R x y z
-/
theorem sbtw_const_sub_iff {x y z : V} (v : V) :
    Sbtw R (v - x) (v - y) (v - z) ↔ Sbtw R x y z :=
  sbtw_const_vsub_iff v

alias ⟨_, Sbtw.const_sub⟩ := sbtw_const_sub_iff

@[simp]
/-
**sbtw_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_neg_iff {x y z : V} : Sbtw R (-x) (-y) (-z) ↔ Sbtw R x y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sbtw_neg_iff {x y z : V} :
    Sbtw R (-x) (-y) (-z) ↔ Sbtw R x y z := by
  simp only [← zero_sub, sbtw_const_sub_iff]

alias ⟨_, Sbtw.neg⟩ := sbtw_neg_iff

@[simp]
/-
**sbtw_vsub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_vsub_const_iff {x y z : P} (p : P) : Sbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p
) ↔ Sbtw R x y z
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_vsub_const_iff`：wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x
 -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_vsub_const_iff {x y z : P} (p : P) :
    Sbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Sbtw R x y z := by
  rw [Sbtw, Sbtw, wbtw_vsub_const_iff, (vsub_left_injective p).ne_iff,
    (vsub_left_injective p).ne_iff]

alias ⟨_, Sbtw.vsub_const⟩ := sbtw_vsub_const_iff

@[simp]
/-
**sbtw_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_sub_const_iff {x y z : V} (v : V) : Sbtw R (x - v) (y - v) (z - v) ↔ 
Sbtw R x y z
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_vsub_const_iff`：sbtw_vsub_const_iff {x y z : P} (p : P) : Sbtw R (x
 -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Sbtw R x y z
-/
theorem sbtw_sub_const_iff {x y z : V} (v : V) :
    Sbtw R (x - v) (y - v) (z - v) ↔ Sbtw R x y z :=
  sbtw_vsub_const_iff v

alias ⟨_, Sbtw.sub_const⟩ := sbtw_sub_const_iff
/-
**Sbtw.wbtw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z :=
  h.1
/-
**Sbtw.ne_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x
参数：h : Sbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y ≠ x :=
  h.2.1
/-
**Sbtw.left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
参数：h : Sbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x ≠ y :=
  h.2.1.symm
/-
**Sbtw.ne_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z
参数：h : Sbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y ≠ z :=
  h.2.2
/-
**Sbtw.right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z != y
参数：h : Sbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z ≠ y :=
  h.2.2.symm

set_option backward.isDefEq.respectTransparency false in
/-
**Sbtw.mem_image_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) : y in lineMap x z '' Se
t.Ioo (0 : R) 1
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`：eq_endpoints_or_mem_Ioo_of_mem_I
cc {x : α} (hmem : x in Icc a b) : x = a ∨ x = b ∨ x in Ioo a b
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
-/
theorem Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) :
    y ∈ lineMap x z '' Set.Ioo (0 : R) 1 := by
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ho)
  · exfalso
    exact hyx (lineMap_apply_zero _ _)
  · exfalso
    exact hyz (lineMap_apply_one _ _)
  · exact ⟨t, ho, rfl⟩
/-
**Wbtw.mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) : y in line[R, x, z]
参数：h : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem_affineSpan_pair`：AffineMap.lineMap_mem_affineSpan_
pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂]
-/
theorem Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) : y ∈ line[R, x, z] := by
  rcases h with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

variable (R)

section OrderedRing

variable [IsOrderedRing R]

@[simp]
/-
**wbtw_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_self_left (x y : P) : Wbtw R x x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_mem_affineSegment`：left_mem_affineSegment (x y : P) : x in affineSe
gment R x y
-/
theorem wbtw_self_left (x y : P) : Wbtw R x x y :=
  left_mem_affineSegment _ _ _

@[simp]
/-
**wbtw_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_self_right (x y : P) : Wbtw R x y y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_mem_affineSegment`：right_mem_affineSegment (x y : P) : y in affine
Segment R x y
-/
theorem wbtw_self_right (x y : P) : Wbtw R x y y :=
  right_mem_affineSegment _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**wbtw_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `wbtw_self_left`：wbtw_self_left (x y : P) : Wbtw R x x y
-/
theorem wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [Wbtw, affineSegment] using h
  · rw [h]
    exact wbtw_self_left R x x

end OrderedRing

section lift

variable [ZeroLEOneClass R]
variable (R' : Type*) [Ring R'] [PartialOrder R']
variable [Module R' V] [Module R' R] [IsScalarTower R' R V] [SMulPosMono R' R]

/-
**affineSegment.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSegment.lift (x y : P) : affineSegment R' x y subseteq affineSegment
 R x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineSegment.lift (x y : P) : affineSegment R' x y ⊆ affineSegment R x y := by
  rintro p ⟨a, ⟨⟨ha₀, ha₁⟩, rfl⟩⟩
  refine ⟨a • 1, ⟨?_, ?_⟩, by simp [lineMap_apply]⟩
  · rw [← zero_smul R' (1 : R)]
    exact smul_le_smul_of_nonneg_right ha₀ zero_le_one
  · nth_rw 2 [← one_smul R' 1]
    exact smul_le_smul_of_nonneg_right ha₁ zero_le_one

variable {R'} in
/-- Lift a `Wbtw` predicate from one ring to another along a scalar tower. -/
/-
**Wbtw.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.lift {x y z : P} (h : Wbtw R' x y z) : Wbtw R x y z
参数：h : Wbtw R' x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSegment.lift`：affineSegment.lift (x y : P) : affineSegment R' x y 
subseteq affineSegment R x y

--- 原说明 ---
Lift a `Wbtw` predicate from one ring to another along a scalar tower.
-/
theorem Wbtw.lift {x y z : P} (h : Wbtw R' x y z) : Wbtw R x y z :=
  affineSegment.lift R R' x z h

variable {R'} in
/-- Lift a `Sbtw` predicate from one ring to another along a scalar tower. -/
/-
**Sbtw.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.lift {x y z : P} (h : Sbtw R' x y z) : Sbtw R x y z
参数：h : Sbtw R' x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.lift`：Wbtw.lift {x y z : P} (h : Wbtw R' x y z) : Wbtw R x y z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Lift a `Sbtw` predicate from one ring to another along a scalar tower.
-/
theorem Sbtw.lift {x y z : P} (h : Sbtw R' x y z) : Sbtw R x y z :=
  ⟨h.wbtw.lift R, h.2⟩

end lift

@[simp]
/-
**not_sbtw_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sbtw_self_left (x y : P) : ¬Sbtw R x x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.ne_left`：Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x
-/
theorem not_sbtw_self_left (x y : P) : ¬Sbtw R x x y :=
  fun h => h.ne_left rfl

@[simp]
/-
**not_sbtw_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sbtw_self_right (x y : P) : ¬Sbtw R x y y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.ne_right`：Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z
-/
theorem not_sbtw_self_right (x y : P) : ¬Sbtw R x y y :=
  fun h => h.ne_right rfl

variable {R}
variable [IsOrderedRing R]
/-
**Wbtw.left_ne_right_of_ne_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.left_ne_right_of_ne_left {x y z : P} (h : Wbtw R x y z) (hne : y != x
) : x != z
参数：h : Wbtw R x y z；hne : y != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_self_iff`：wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x
-/
theorem Wbtw.left_ne_right_of_ne_left {x y z : P} (h : Wbtw R x y z) (hne : y ≠ x) : x ≠ z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h
/-
**Wbtw.left_ne_right_of_ne_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.left_ne_right_of_ne_right {x y z : P} (h : Wbtw R x y z) (hne : y != 
z) : x != z
参数：h : Wbtw R x y z；hne : y != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_self_iff`：wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x
-/
theorem Wbtw.left_ne_right_of_ne_right {x y z : P} (h : Wbtw R x y z) (hne : y ≠ z) : x ≠ z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h
/-
**Sbtw.left_ne_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : x != z
参数：h : Sbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.left_ne_right_of_ne_left`：Wbtw.left_ne_right_of_ne_left {x y z : P}
 (h : Wbtw R x y z) (hne : y != x) : x != z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : x ≠ z :=
  h.wbtw.left_ne_right_of_ne_left h.2.1

variable (R) in
@[simp]
/-
**not_sbtw_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sbtw_self (x y : P) : ¬Sbtw R x y x
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
-/
theorem not_sbtw_self (x y : P) : ¬Sbtw R x y x :=
  fun h => h.left_ne_right rfl

omit [IsOrderedRing R] in
@[simp]
/-
**wbtw_zero_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_zero_one_iff {x : R} : Wbtw R 0 x 1 ↔ x in Set.Icc (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.lineMap_apply_ring`：lineMap_apply_ring (a b c : k) : lineMap a
 b c = (1 - c) * a + c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wbtw_zero_one_iff {x : R} : Wbtw R 0 x 1 ↔ x ∈ Set.Icc (0 : R) 1 := by
  rw [Wbtw, affineSegment, Set.mem_image]
  simp_rw [lineMap_apply_ring]
  simp

@[simp]
/-
**wbtw_one_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_one_zero_iff {x : R} : Wbtw R 1 x 0 ↔ x in Set.Icc (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `wbtw_zero_one_iff`：wbtw_zero_one_iff {x : R} : Wbtw R 0 x 1 ↔ x in Set.I
cc (0 : R) 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wbtw_one_zero_iff {x : R} : Wbtw R 1 x 0 ↔ x ∈ Set.Icc (0 : R) 1 := by
  rw [wbtw_comm, wbtw_zero_one_iff]

omit [IsOrderedRing R] in
@[simp]
/-
**sbtw_zero_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_zero_one_iff {x : R} : Sbtw R 0 x 1 ↔ x in Set.Ioo (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_zero_one_iff`：wbtw_zero_one_iff {x : R} : Wbtw R 0 x 1 ↔ x in Set.I
cc (0 : R) 1
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem sbtw_zero_one_iff {x : R} : Sbtw R 0 x 1 ↔ x ∈ Set.Ioo (0 : R) 1 := by
  rw [Sbtw, wbtw_zero_one_iff, Set.mem_Icc, Set.mem_Ioo]
  exact
    ⟨fun h => ⟨h.1.1.lt_of_ne (Ne.symm h.2.1), h.1.2.lt_of_ne h.2.2⟩, fun h =>
      ⟨⟨h.1.le, h.2.le⟩, h.1.ne', h.2.ne⟩⟩

@[simp]
/-
**sbtw_one_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_one_zero_iff {x : R} : Sbtw R 1 x 0 ↔ x in Set.Ioo (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sbtw_comm`：sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x
· 使用定理 `sbtw_zero_one_iff`：sbtw_zero_one_iff {x : R} : Sbtw R 0 x 1 ↔ x in Set.I
oo (0 : R) 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_one_zero_iff {x : R} : Sbtw R 1 x 0 ↔ x ∈ Set.Ioo (0 : R) 1 := by
  rw [sbtw_comm, sbtw_zero_one_iff]
/-
**Wbtw.trans_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wb
tw R w x z
参数：h₁ : Wbtw R w y z；h₂ : Wbtw R w x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wbtw R w x z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one₀ ht₂.2 ht₁.1 ht₁.2⟩, ?_⟩
  rw [lineMap_apply, lineMap_apply, lineMap_vsub_left, smul_smul]
/-
**Wbtw.trans_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_right {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) : W
btw R w y z
参数：h₁ : Wbtw R w x z；h₂ : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `Wbtw.trans_left`：Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ :
 Wbtw R w x y) : Wbtw R w x z
-/
theorem Wbtw.trans_right {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) : Wbtw R w y z := by
  rw [wbtw_comm] at *
  exact h₁.trans_left h₂

section IsTorsionFree
variable [IsDomain R] [IsTorsionFree R V] {w x y z : P} {r : R}

set_option backward.isDefEq.respectTransparency false in
/-
**sbtw_iff_mem_image_Ioo_and_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_iff_mem_image_Ioo_and_ne : Sbtw R x y z ↔ y in lineMap x z '' Set.Ioo
 (0 : R) 1 ∧ x != z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.mem_image_Ioo`：Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) : 
y in lineMap x z '' Set.Ioo (0 : R) 1
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem sbtw_iff_mem_image_Ioo_and_ne :
    Sbtw R x y z ↔ y ∈ lineMap x z '' Set.Ioo (0 : R) 1 ∧ x ≠ z := by
  refine ⟨fun h => ⟨h.mem_image_Ioo, h.left_ne_right⟩, fun h => ?_⟩
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩
  refine ⟨⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩, ?_⟩
  rw [lineMap_apply, ← @vsub_ne_zero V, ← @vsub_ne_zero V _ _ _ _ z, vadd_vsub_assoc, vsub_self,
    vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev z x, ← @neg_one_smul R, ← add_smul, ← sub_eq_add_neg]
  simp [sub_eq_zero, ht.1.ne.symm, ht.2.ne, hxz.symm]

variable (R z) in
/-
**wbtw_swap_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_swap_left_iff : Wbtw R x y z ∧ Wbtw R y x z ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `AddSemigroupAction.add_vadd`：∀ {G : Type u_9} {P : Type u_10} {inst : Ad
dSemigroup G} [self : AddSemigroupAction G P] (g₁ g₂ : G) (p : P),   (g₁ + g₂) +
ᵥ p = g₁ +ᵥ g₂ +ᵥ…
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Left.neg_nonpos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
（共 33 条，此处仅展示前 30 条）
-/
theorem wbtw_swap_left_iff : Wbtw R x y z ∧ Wbtw R y x z ↔ x = y := by
  constructor
  · rintro ⟨hxyz, hyxz⟩
    rcases hxyz with ⟨ty, hty, rfl⟩
    rcases hyxz with ⟨tx, htx, hx⟩
    rw [lineMap_apply, lineMap_apply, ← add_vadd] at hx
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul, ← sub_smul,
      ← add_smul, smul_eq_zero] at hx
    rcases hx with (h | h)
    · nth_rw 1 [← mul_one tx] at h
      rw [← mul_sub, add_eq_zero_iff_neg_eq] at h
      have h' : ty = 0 := by
        refine le_antisymm ?_ hty.1
        rw [← h, Left.neg_nonpos_iff]
        exact mul_nonneg htx.1 (sub_nonneg.2 hty.2)
      simp [h']
    · rw [vsub_eq_zero_iff_eq] at h
      rw [h, lineMap_same_apply]
  · rintro rfl
    exact ⟨wbtw_self_left _ _ _, wbtw_self_left _ _ _⟩

variable (R x) in
/-
**wbtw_swap_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔ y = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `wbtw_swap_left_iff`：wbtw_swap_left_iff : Wbtw R x y z ∧ Wbtw R y x z ↔ x
 = y
-/
theorem wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔ y = z := by
  rw [wbtw_comm, wbtw_comm (z := y), eq_comm]
  exact wbtw_swap_left_iff R x

variable (R x) in
/-
**wbtw_rotate_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_rotate_iff (x : P) : Wbtw R x y z ∧ Wbtw R z x y ↔ x = y
参数：x : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `wbtw_swap_right_iff`：wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔
 y = z
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wbtw_rotate_iff (x : P) : Wbtw R x y z ∧ Wbtw R z x y ↔ x = y := by
  rw [wbtw_comm, wbtw_swap_right_iff, eq_comm]
/-
**Wbtw.swap_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.swap_left_iff (h : Wbtw R x y z) : Wbtw R y x z ↔ x = y
参数：h : Wbtw R x y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wbtw_swap_left_iff`：wbtw_swap_left_iff : Wbtw R x y z ∧ Wbtw R y x z ↔ x
 = y
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Wbtw.swap_left_iff (h : Wbtw R x y z) : Wbtw R y x z ↔ x = y := by
  rw [← wbtw_swap_left_iff R z, and_iff_right h]
/-
**Wbtw.swap_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.swap_right_iff (h : Wbtw R x y z) : Wbtw R x z y ↔ y = z
参数：h : Wbtw R x y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wbtw_swap_right_iff`：wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔
 y = z
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Wbtw.swap_right_iff (h : Wbtw R x y z) : Wbtw R x z y ↔ y = z := by
  rw [← wbtw_swap_right_iff R x, and_iff_right h]
/-
**Wbtw.rotate_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.rotate_iff (h : Wbtw R x y z) : Wbtw R z x y ↔ x = y
参数：h : Wbtw R x y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wbtw_rotate_iff`：wbtw_rotate_iff (x : P) : Wbtw R x y z ∧ Wbtw R z x y ↔
 x = y
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Wbtw.rotate_iff (h : Wbtw R x y z) : Wbtw R z x y ↔ x = y := by
  rw [← wbtw_rotate_iff R x, and_iff_right h]
/-
**Sbtw.not_swap_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.not_swap_left (h : Sbtw R x y z) : ¬Wbtw R y x z
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Wbtw.swap_left_iff`：Wbtw.swap_left_iff (h : Wbtw R x y z) : Wbtw R y x z
 ↔ x = y
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
-/
theorem Sbtw.not_swap_left (h : Sbtw R x y z) : ¬Wbtw R y x z := fun hs =>
  h.left_ne (h.wbtw.swap_left_iff.1 hs)
/-
**Sbtw.not_swap_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.not_swap_right (h : Sbtw R x y z) : ¬Wbtw R x z y
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.ne_right`：Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Wbtw.swap_right_iff`：Wbtw.swap_right_iff (h : Wbtw R x y z) : Wbtw R x z
 y ↔ y = z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
-/
theorem Sbtw.not_swap_right (h : Sbtw R x y z) : ¬Wbtw R x z y := fun hs =>
  h.ne_right (h.wbtw.swap_right_iff.1 hs)
/-
**Sbtw.not_rotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.not_rotate (h : Sbtw R x y z) : ¬Wbtw R z x y
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Wbtw.rotate_iff`：Wbtw.rotate_iff (h : Wbtw R x y z) : Wbtw R z x y ↔ x =
 y
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
-/
theorem Sbtw.not_rotate (h : Sbtw R x y z) : ¬Wbtw R z x y := fun hs =>
  h.left_ne (h.wbtw.rotate_iff.1 hs)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**wbtw_lineMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_lineMap_iff : Wbtw R x (lineMap x y r) y ↔ x = y ∨ r in Set.Icc (0 : 
R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_same_apply`：lineMap_same_apply (p : P1) (c : k) : line
Map p p c = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `AffineMap.lineMap_injective`：lineMap_injective [IsDomain k] [IsTorsionFr
ee k V1] {p₀ p₁ : P1} (h : p₀ != p₁) : Function.Injective (lineMap p₀ p₁ : k -> 
P1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wbtw_lineMap_iff :
    Wbtw R x (lineMap x y r) y ↔ x = y ∨ r ∈ Set.Icc (0 : R) 1 := by
  by_cases hxy : x = y
  · rw [hxy, lineMap_same_apply]
    simp
  rw [or_iff_right hxy, Wbtw, affineSegment, (lineMap_injective R hxy).mem_set_image]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**sbtw_lineMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_lineMap_iff : Sbtw R x (lineMap x y r) y ↔ x != y ∧ r in Set.Ioo (0 :
 R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sbtw_iff_mem_image_Ioo_and_ne`：sbtw_iff_mem_image_Ioo_and_ne : Sbtw R x 
y z ↔ y in lineMap x z '' Set.Ioo (0 : R) 1 ∧ x != z
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `AffineMap.lineMap_injective`：lineMap_injective [IsDomain k] [IsTorsionFr
ee k V1] {p₀ p₁ : P1} (h : p₀ != p₁) : Function.Injective (lineMap p₀ p₁ : k -> 
P1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_lineMap_iff :
    Sbtw R x (lineMap x y r) y ↔ x ≠ y ∧ r ∈ Set.Ioo (0 : R) 1 := by
  rw [sbtw_iff_mem_image_Ioo_and_ne, and_comm, and_congr_right]
  intro hxy
  rw [(lineMap_injective R hxy).mem_set_image]

@[simp]
/-
**wbtw_mul_sub_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_mul_sub_add_iff {x y r : R} : Wbtw R x (r * (y - x) + x) y ↔ x = y ∨ 
r in Set.Icc (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_lineMap_iff`：wbtw_lineMap_iff : Wbtw R x (lineMap x y r) y ↔ x = y 
∨ r in Set.Icc (0 : R) 1
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem wbtw_mul_sub_add_iff {x y r : R} :
    Wbtw R x (r * (y - x) + x) y ↔ x = y ∨ r ∈ Set.Icc (0 : R) 1 :=
  wbtw_lineMap_iff

@[simp]
/-
**sbtw_mul_sub_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_mul_sub_add_iff {x y r : R} : Sbtw R x (r * (y - x) + x) y ↔ x != y ∧
 r in Set.Ioo (0 : R) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_lineMap_iff`：sbtw_lineMap_iff : Sbtw R x (lineMap x y r) y ↔ x != y
 ∧ r in Set.Ioo (0 : R) 1
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem sbtw_mul_sub_add_iff {x y r : R} :
    Sbtw R x (r * (y - x) + x) y ↔ x ≠ y ∧ r ∈ Set.Ioo (0 : R) 1 :=
  sbtw_lineMap_iff
/-
**Wbtw.trans_sbtw_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_sbtw_left (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x 
z
参数：h₁ : Wbtw R w y z；h₂ : Sbtw R w x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_left`：Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ :
 Wbtw R w x y) : Wbtw R w x z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.ne_left`：Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x
· 使用定理 `Sbtw.right_ne`：Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wbtw_swap_right_iff`：wbtw_swap_right_iff : Wbtw R x y z ∧ Wbtw R x z y ↔
 y = z
-/
theorem Wbtw.trans_sbtw_left (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z := by
  refine ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, ?_⟩
  rintro rfl
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)
/-
**Wbtw.trans_sbtw_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_sbtw_right (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y
 z
参数：h₁ : Wbtw R w x z；h₂ : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sbtw_comm`：sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x
· 使用定理 `Wbtw.trans_sbtw_left`：Wbtw.trans_sbtw_left (h₁ : Wbtw R w y z) (h₂ : Sbt
w R w x y) : Sbtw R w x z
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
-/
theorem Wbtw.trans_sbtw_right (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y z := by
  rw [wbtw_comm] at *
  rw [sbtw_comm] at *
  exact h₁.trans_sbtw_left h₂
/-
**Sbtw.trans_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_left (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z
参数：h₁ : Sbtw R w y z；h₂ : Sbtw R w x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_sbtw_left`：Wbtw.trans_sbtw_left (h₁ : Wbtw R w y z) (h₂ : Sbt
w R w x y) : Sbtw R w x z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
-/
theorem Sbtw.trans_left (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z :=
  h₁.wbtw.trans_sbtw_left h₂
/-
**Sbtw.trans_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_right (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y z
参数：h₁ : Sbtw R w x z；h₂ : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_sbtw_right`：Wbtw.trans_sbtw_right (h₁ : Wbtw R w x z) (h₂ : S
btw R x y z) : Sbtw R w y z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
-/
theorem Sbtw.trans_right (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w y z :=
  h₁.wbtw.trans_sbtw_right h₂
/-
**Wbtw.trans_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_left_ne (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) (h : y != z) : 
x != z
参数：h₁ : Wbtw R w y z；h₂ : Wbtw R w x y；h : y != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Wbtw.swap_right_iff`：Wbtw.swap_right_iff (h : Wbtw R x y z) : Wbtw R x z
 y ↔ y = z
-/
theorem Wbtw.trans_left_ne (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) (h : y ≠ z) : x ≠ z := by
  rintro rfl
  exact h (h₁.swap_right_iff.1 h₂)
/-
**Wbtw.trans_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_right_ne (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) (h : w != x) :
 w != y
参数：h₁ : Wbtw R w x z；h₂ : Wbtw R x y z；h : w != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Wbtw.swap_left_iff`：Wbtw.swap_left_iff (h : Wbtw R x y z) : Wbtw R y x z
 ↔ x = y
-/
theorem Wbtw.trans_right_ne (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) (h : w ≠ x) : w ≠ y := by
  rintro rfl
  exact h (h₁.swap_left_iff.1 h₂)
/-
**Sbtw.trans_wbtw_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_wbtw_left_ne (h₁ : Sbtw R w y z) (h₂ : Wbtw R w x y) : x != z
参数：h₁ : Sbtw R w y z；h₂ : Wbtw R w x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_left_ne`：Wbtw.trans_left_ne (h₁ : Wbtw R w y z) (h₂ : Wbtw R 
w x y) (h : y != z) : x != z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.ne_right`：Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z
-/
theorem Sbtw.trans_wbtw_left_ne (h₁ : Sbtw R w y z) (h₂ : Wbtw R w x y) : x ≠ z :=
  h₁.wbtw.trans_left_ne h₂ h₁.ne_right
/-
**Sbtw.trans_wbtw_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_wbtw_right_ne (h₁ : Sbtw R w x z) (h₂ : Wbtw R x y z) : w != y
参数：h₁ : Sbtw R w x z；h₂ : Wbtw R x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_right_ne`：Wbtw.trans_right_ne (h₁ : Wbtw R w x z) (h₂ : Wbtw 
R x y z) (h : w != x) : w != y
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
-/
theorem Sbtw.trans_wbtw_right_ne (h₁ : Sbtw R w x z) (h₂ : Wbtw R x y z) : w ≠ y :=
  h₁.wbtw.trans_right_ne h₂ h₁.left_ne

end IsTorsionFree

/-
**Sbtw.affineCombination_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.affineCombination_of_mem_affineSpan_pair [IsDomain R] [IsTorsionFree 
R V] {ι : Type*} {p : ι -> P} (ha : AffineIndependent R p) {w w₁ w₂ : ι -> R} {s
 : Finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s
, w₂ i = 1) (h : s.affineCombination R p w in line[R, s.affineCombination R p w₁
, s.affineCombination R p w₂]) {i : ι} (his : i in s) (hs : Sbtw R (w₁ i) (w i) 
(w₂ i)) : Sbtw R (s.affineCombination R p w₁) (s.affineCombination R p w) (s.aff
ineCombination R p w₂)
参数：ha : AffineIndependent R p；hw : ∑ i in s, w i = 1；hw₁ : ∑ i in s, w₁ i = 1；hw
₂ : ∑ i in s, w₂ i = 1；h : s.affineCombination R p w in line[R, s.affineCombinat
ion R p w₁, s.affineCombination R p w₂]；his : i in s；hs : Sbtw R (w₁ i) (w i) (w
₂ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineCombination_mem_affineSpan_pair`：affineCombination_mem_affineSpan_
pair {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} 
(_ : ∑ i in s, w i = 1) (hw…
· 使用定理 `Finset.affineCombination_congr`：affineCombination_congr {w₁ w₂ : ι -> k}
 (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = 
p₂ i) : s.affineComb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用定理 `Finset.weightedVSub_const_smul`：weightedVSub_const_smul (w : ι -> k) (p 
: ι -> P) (c : k) : s.weightedVSub p (c • w) = c • s.weightedVSub p w
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `sbtw_lineMap_iff`：sbtw_lineMap_iff : Sbtw R x (lineMap x y r) y ↔ x != y
 ∧ r in Set.Ioo (0 : R) 1
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sbtw_mul_sub_add_iff`：sbtw_mul_sub_add_iff {x y r : R} : Sbtw R x (r * (
y - x) + x) y ↔ x != y ∧ r in Set.Ioo (0 : R) 1
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
-/
theorem Sbtw.affineCombination_of_mem_affineSpan_pair [IsDomain R] [IsTorsionFree R V]
    {ι : Type*} {p : ι → P} (ha : AffineIndependent R p) {w w₁ w₂ : ι → R} {s : Finset ι}
    (hw : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1)
    (h : s.affineCombination R p w ∈
      line[R, s.affineCombination R p w₁, s.affineCombination R p w₂])
    {i : ι} (his : i ∈ s) (hs : Sbtw R (w₁ i) (w i) (w₂ i)) :
    Sbtw R (s.affineCombination R p w₁) (s.affineCombination R p w)
      (s.affineCombination R p w₂) := by
  rw [affineCombination_mem_affineSpan_pair ha hw hw₁ hw₂] at h
  rcases h with ⟨r, hr⟩
  rw [hr i his, sbtw_mul_sub_add_iff] at hs
  change ∀ i ∈ s, w i = (r • (w₂ - w₁) + w₁) i at hr
  rw [s.affineCombination_congr hr fun _ _ => rfl]
  rw [← s.weightedVSub_vadd_affineCombination, s.weightedVSub_const_smul,
    ← s.affineCombination_vsub, ← lineMap_apply, sbtw_lineMap_iff, and_iff_left hs.2,
    ← @vsub_ne_zero V, s.affineCombination_vsub]
  intro hz
  have hw₁w₂ : (∑ i ∈ s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, hw₁, hw₂, sub_self]
  refine hs.1 ?_
  have ha' := ha s (w₁ - w₂) hw₁w₂ hz i his
  rwa [Pi.sub_apply, sub_eq_zero] at ha'

namespace Affine

namespace Simplex

/-- The closed interior of a 1-simplex is a segment between its vertices. -/
/-
**Affine.Simplex.closedInterior_eq_affineSegment** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：closedInterior_eq_affineSegment (s : Simplex R P 1) : s.closedInterior = a
ffineSegment R (s.points 0) (s.points 1)
参数：s : Simplex R P 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_left`：affineCombinationLine
MapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineCom
binationLineMapWeights i j c i = 1 - c
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_right`：affineCombinationLin
eMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineC
ombinationLineMapWeights i j c j = c
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `Finset.sum_affineCombinationLineMapWeights`：sum_affineCombinationLineMap
Weights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) (c : k) : ∑ t in s
, affineCombinationLineMapWeight…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The closed interior of a 1-simplex is a segment between its vertices.
-/
lemma closedInterior_eq_affineSegment (s : Simplex R P 1) :
    s.closedInterior = affineSegment R (s.points 0) (s.points 1) := by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h, Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]
    exact Set.mem_image_of_mem _ (h01 _)
  · rintro ⟨r, ⟨h0, h1⟩, rfl⟩
    rw [← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _), affineCombination_mem_closedInterior_iff
        (Finset.sum_affineCombinationLineMapWeights _ (Finset.mem_univ _) (Finset.mem_univ _) _)]
    intro i
    fin_cases i <;> simp [h0, h1]

/-- A point lies in the closed interior of a 1-simplex if and only if it lies weakly between its
vertices. -/
/-
**Affine.Simplex.mem_closedInterior_iff_wbtw** 是 Mathlib 中的一个引理，位于命名空间 `Affine.S
implex`。
形式化陈述：mem_closedInterior_iff_wbtw {s : Simplex R P 1} {p : P} : p in s.closedInt
erior ↔ Wbtw R (s.points 0) p (s.points 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.closedInterior_eq_affineSegment`：closedInterior_eq_affine
Segment (s : Simplex R P 1) : s.closedInterior = affineSegment R (s.points 0) (s
.points 1)
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point lies in the closed interior of a 1-simplex if and only if it lies weakly
 between its
vertices.
-/
lemma mem_closedInterior_iff_wbtw {s : Simplex R P 1} {p : P} :
    p ∈ s.closedInterior ↔ Wbtw R (s.points 0) p (s.points 1) := by
  rw [closedInterior_eq_affineSegment, Wbtw]

/-- The closed interior of a 1-dimensional face of a simplex is a segment between its vertices. -/
/-
**Affine.Simplex.closedInterior_face_eq_affineSegment** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Simplex`。
形式化陈述：closedInterior_face_eq_affineSegment {n : Nat} (s : Simplex R P n) {i j : 
Fin (n + 1)} (h : i != j) : (s.face (Finset.card_pair h)).closedInterior = affin
eSegment R (s.points i) (s.points j)
参数：s : Simplex R P n；n + 1；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `affineSegment_comm`：affineSegment_comm (x y : P) : affineSegment R x y =
 affineSegment R y x
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Simplex.closedInterior_eq_affineSegment`：closedInterior_eq_affine
Segment (s : Simplex R P 1) : s.closedInterior = affineSegment R (s.points 0) (s
.points 1)
· 使用定理 `Affine.Simplex.face_points`：face_points {n : Nat} (s : Simplex k P n) {f
s : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) (i : Fin (m + 1)) : (s.fac
e h).points i = …
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Finset.min'_pair`：∀ {α : Type u_2} [inst : LinearOrder α] (a b : α), {a,
 b}.min' ⋯ = min a b
· 使用定理 `Finset.orderEmbOfFin_zero`：orderEmbOfFin_zero {s : Finset α} {k : Nat} (
h : s.card = k) (hz : 0 < k) : orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (
h.symm ▸ hz))
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The closed interior of a 1-dimensional face of a simplex is a segment between it
s vertices.
-/
lemma closedInterior_face_eq_affineSegment {n : ℕ} (s : Simplex R P n) {i j : Fin (n + 1)}
    (h : i ≠ j) :
    (s.face (Finset.card_pair h)).closedInterior = affineSegment R (s.points i) (s.points j) := by
  have h' : affineSegment R (s.points i) (s.points j) =
      affineSegment R (s.points (min i j)) (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [affineSegment_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h', (s.face (Finset.card_pair h)).closedInterior_eq_affineSegment, face_points, face_points]
  congr 2
  · convert! Finset.orderEmbOfFin_zero _ _
    · exact (Finset.min'_pair i j).symm
    · lia
  · convert! Finset.orderEmbOfFin_last _ _
    · exact (Finset.max'_pair i j).symm
    · lia

/-- A point lies in the closed interior of a 1-dimensional face of a simplex if and only if it lies
weakly between its vertices. -/
/-
**Affine.Simplex.mem_closedInterior_face_iff_wbtw** 是 Mathlib 中的一个引理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：mem_closedInterior_face_iff_wbtw {n : Nat} (s : Simplex R P n) {p : P} {i 
j : Fin (n + 1)} (h : i != j) : p in (s.face (Finset.card_pair h)).closedInterio
r ↔ Wbtw R (s.points i) p (s.points j)
参数：s : Simplex R P n；n + 1；h : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.closedInterior_face_eq_affineSegment`：closedInterior_face
_eq_affineSegment {n : Nat} (s : Simplex R P n) {i j : Fin (n + 1)} (h : i != j)
 : (s.face (Finset.card_pair h)).closedIn…
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point lies in the closed interior of a 1-dimensional face of a simplex if and 
only if it lies
weakly between its vertices.
-/
lemma mem_closedInterior_face_iff_wbtw {n : ℕ} (s : Simplex R P n) {p : P} {i j : Fin (n + 1)}
    (h : i ≠ j) :
    p ∈ (s.face (Finset.card_pair h)).closedInterior ↔ Wbtw R (s.points i) p (s.points j) := by
  rw [s.closedInterior_face_eq_affineSegment h, Wbtw]

set_option backward.isDefEq.respectTransparency false in
/-- The interior of a 1-simplex is a segment between its vertices. -/
/-
**Affine.Simplex.interior_eq_image_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：interior_eq_image_Ioo (s : Simplex R P 1) : s.interior = AffineMap.lineMap
 (s.points 0) (s.points 1) '' Set.Ioo (0 : R) 1
参数：s : Simplex R P 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_left`：affineCombinationLine
MapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineCom
binationLineMapWeights i j c i = 1 - c
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_right`：affineCombinationLin
eMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineC
ombinationLineMapWeights i j c j = c
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_iff`：affineCombination_mem
_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w 
i = 1) : Finset.univ.affineCombination …
· 使用定理 `Finset.sum_affineCombinationLineMapWeights`：sum_affineCombinationLineMap
Weights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) (c : k) : ∑ t in s
, affineCombinationLineMapWeight…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The interior of a 1-simplex is a segment between its vertices.
-/
lemma interior_eq_image_Ioo (s : Simplex R P 1) :
    s.interior = AffineMap.lineMap (s.points 0) (s.points 1) '' Set.Ioo (0 : R) 1 := by
  ext p
  constructor
  · rintro ⟨w, hw, h01, rfl⟩
    have h : w = Finset.affineCombinationLineMapWeights 0 1 (w 1) := by
      rw [Fin.sum_univ_two] at hw
      ext i
      fin_cases i <;> simp [← hw]
    rw [h, Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _)]
    exact Set.mem_image_of_mem _ (h01 _)
  · rintro ⟨r, ⟨h0, h1⟩, rfl⟩
    rw [← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
      (Finset.mem_univ _), affineCombination_mem_interior_iff
        (Finset.sum_affineCombinationLineMapWeights _ (Finset.mem_univ _) (Finset.mem_univ _) _)]
    intro i
    fin_cases i <;> simp [h0, h1]

/-- A point lies in the interior of a 1-simplex if and only if it lies strictly between its
vertices. -/
/-
**Affine.Simplex.mem_interior_iff_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：mem_interior_iff_sbtw [IsDomain R] [IsTorsionFree R V] {s : Simplex R P 1}
 {p : P} : p in s.interior ↔ Sbtw R (s.points 0) p (s.points 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.interior_eq_image_Ioo`：interior_eq_image_Ioo (s : Simplex
 R P 1) : s.interior = AffineMap.lineMap (s.points 0) (s.points 1) '' Set.Ioo (0
 : R) 1
· 使用定理 `sbtw_iff_mem_image_Ioo_and_ne`：sbtw_iff_mem_image_Ioo_and_ne : Sbtw R x 
y z ↔ y in lineMap x z '' Set.Ioo (0 : R) 1 ∧ x != z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point lies in the interior of a 1-simplex if and only if it lies strictly betw
een its
vertices.
-/
lemma mem_interior_iff_sbtw [IsDomain R] [IsTorsionFree R V] {s : Simplex R P 1} {p : P} :
    p ∈ s.interior ↔ Sbtw R (s.points 0) p (s.points 1) := by
  rw [interior_eq_image_Ioo, sbtw_iff_mem_image_Ioo_and_ne]
  simp [s.independent.injective.ne (by decide : (0 : Fin 2) ≠ 1)]

/-- A point lies in the interior of a 1-dimensional face of a simplex if and only if it lies
strictly between its vertices. -/
/-
**Affine.Simplex.mem_interior_face_iff_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：mem_interior_face_iff_sbtw [IsDomain R] [IsTorsionFree R V] {n : Nat} (s :
 Simplex R P n) {p : P} {i j : Fin (n + 1)} (h : i != j) : p in (s.face (Finset.
card_pair h)).interior ↔ Sbtw R (s.points i) p (s.points j)
参数：s : Simplex R P n；n + 1；h : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `sbtw_comm`：sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Simplex.mem_interior_iff_sbtw`：mem_interior_iff_sbtw [IsDomain R]
 [IsTorsionFree R V] {s : Simplex R P 1} {p : P} : p in s.interior ↔ Sbtw R (s.p
oints 0) p (s.points 1)
· 使用定理 `Affine.Simplex.face_points`：face_points {n : Nat} (s : Simplex k P n) {f
s : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) (i : Fin (m + 1)) : (s.fac
e h).points i = …
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Finset.min'_pair`：∀ {α : Type u_2} [inst : LinearOrder α] (a b : α), {a,
 b}.min' ⋯ = min a b
· 使用定理 `Finset.orderEmbOfFin_zero`：orderEmbOfFin_zero {s : Finset α} {k : Nat} (
h : s.card = k) (hz : 0 < k) : orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (
h.symm ▸ hz))
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A point lies in the interior of a 1-dimensional face of a simplex if and only if
 it lies
strictly between its vertices.
-/
lemma mem_interior_face_iff_sbtw [IsDomain R] [IsTorsionFree R V] {n : ℕ}
    (s : Simplex R P n) {p : P} {i j : Fin (n + 1)} (h : i ≠ j) :
    p ∈ (s.face (Finset.card_pair h)).interior ↔ Sbtw R (s.points i) p (s.points j) := by
  have h' : Sbtw R (s.points i) p (s.points j) ↔
      Sbtw R (s.points (min i j)) p (s.points (max i j)) := by
    rcases h.lt_or_gt with hij | hji
    · simp [min_eq_left hij.le, max_eq_right hij.le]
    · nth_rw 2 [sbtw_comm]
      simp [max_eq_left hji.le, min_eq_right hji.le]
  rw [h', mem_interior_iff_sbtw, face_points, face_points]
  congr! 4
  · convert! Finset.orderEmbOfFin_zero _ _
    · exact (Finset.min'_pair i j).symm
    · lia
  · convert! Finset.orderEmbOfFin_last _ _
    · exact (Finset.max'_pair i j).symm
    · lia

end Simplex

end Affine

end OrderedRing

section StrictOrderedCommRing

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {R}

/-
**Wbtw.sameRay_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.sameRay_vsub {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -
ᵥ y)
参数：h : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `sameRay_of_mem_segment`：sameRay_of_mem_segment [CommRing 𝕜] [PartialOrde
r 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E} (h : x in
 [y -[𝕜] z])…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `mem_segment_iff_wbtw`：mem_segment_iff_wbtw {x y z : V} : y in segment R 
x z ↔ Wbtw R x y z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Wbtw.vsub_const`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : 
Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.M
odule…
-/
theorem Wbtw.sameRay_vsub {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ y) := by
  simpa using sameRay_of_mem_segment ((mem_segment_iff_wbtw).2 (h.vsub_const x))
/-
**Wbtw.sameRay_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.sameRay_vsub_left {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x)
 (z -ᵥ x)
参数：h : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `SameRay.sameRay_nonneg_smul_left`：sameRay_nonneg_smul_left (v : M) (ha :
 0 <= a) : SameRay R (a • v) v
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem Wbtw.sameRay_vsub_left {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ x) := by
  rcases h with ⟨t, ⟨ht0, _⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_left (z -ᵥ x) ht0]
/-
**Wbtw.sameRay_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.sameRay_vsub_right {x y z : P} (h : Wbtw R x y z) : SameRay R (z -ᵥ x
) (z -ᵥ y)
参数：h : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `AffineMap.right_vsub_lineMap`：right_vsub_lineMap (p₀ p₁ : P1) (c : k) : 
p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
-/
theorem Wbtw.sameRay_vsub_right {x y z : P} (h : Wbtw R x y z) : SameRay R (z -ᵥ x) (z -ᵥ y) := by
  rcases h with ⟨t, ⟨_, ht1⟩, rfl⟩
  simp [SameRay.sameRay_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)]

end StrictOrderedCommRing

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {R}

/-- Suppose lines from two vertices of a triangle to interior points of the opposite side meet at
`p`. Then `p` lies in the interior of the first (and by symmetry the other) segment from a
vertex to the point on the opposite side. -/
/-
**sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair [IsTorsionFree R V] {t : Affin
e.Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) {p₁ p₂ p : P} (h₁ : Sbtw R (
t.points i₂) p₁ (t.points i₃)) (h₂ : Sbtw R (t.points i₁) p₂ (t.points i₃)) (h₁'
 : p in line[R, t.points i₁, p₁]) (h₂' : p in line[R, t.points i₂, p₂]) : Sbtw R
 (t.points i₁) p p₁
参数：h₁₂ : i₁ != i₂；h₁ : Sbtw R (t.points i₂) p₁ (t.points i₃)；h₂ : Sbtw R (t.poin
ts i₁) p₂ (t.points i₃)；h₁' : p in line[R, t.points i₁, p₁]；h₂' : p in line[R, t
.points i₂, p₂]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `AffineSubspace.le_def'`：le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ 
↔ forall p in s₁, p in s₂
· 使用定理 `Wbtw.mem_affineSpan`：Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) 
: y in line[R, x, z]
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.mem_image_Ioo`：Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) : 
y in lineMap x z '' Set.Ioo (0 : R) 1
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `sign_eq_of_affineCombination_mem_affineSpan_single_lineMap`：sign_eq_of_a
ffineCombination_mem_affineSpan_single_lineMap {p : ι -> P} (h : AffineIndepende
nt k p) {w : ι -> k} {s : Finset ι} (hw : ∑ i in…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `Sbtw.affineCombination_of_mem_affineSpan_pair`：Sbtw.affineCombination_of
_mem_affineSpan_pair [IsDomain R] [IsTorsionFree R V] {ι : Type*} {p : ι -> P} (
ha : AffineIndependent R p) {w w₁ w…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `Finset.sum_affineCombinationLineMapWeights`：sum_affineCombinationLineMap
Weights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) (c : k) : ∑ t in s
, affineCombinationLineMapWeight…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose lines from two vertices of a triangle to interior points of the opposite
 side meet at
`p`. Then `p` lies in the interior of the first (and by symmetry the other) segm
ent from a
vertex to the point on the opposite side.
-/
theorem sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair [IsTorsionFree R V]
    {t : Affine.Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) {p₁ p₂ p : P}
    (h₁ : Sbtw R (t.points i₂) p₁ (t.points i₃)) (h₂ : Sbtw R (t.points i₁) p₂ (t.points i₃))
    (h₁' : p ∈ line[R, t.points i₁, p₁]) (h₂' : p ∈ line[R, t.points i₂, p₂]) :
    Sbtw R (t.points i₁) p p₁ := by
  have h₁₃ : i₁ ≠ i₃ := by
    rintro rfl
    simp at h₂
  have h₂₃ : i₂ ≠ i₃ := by
    rintro rfl
    simp at h₁
  have h3 : ∀ i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by lia
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
    clear h₁ h₂ h₁' h₂'
    decide +revert
  have hp : p ∈ affineSpan R (Set.range t.points) := by
    have hle : line[R, t.points i₁, p₁] ≤ affineSpan R (Set.range t.points) := by
      refine affineSpan_pair_le_of_mem_of_mem (mem_affineSpan R (Set.mem_range_self _)) ?_
      have hle : line[R, t.points i₂, t.points i₃] ≤ affineSpan R (Set.range t.points) := by
        refine affineSpan_mono R ?_
        simp [Set.insert_subset_iff]
      rw [AffineSubspace.le_def'] at hle
      exact hle _ h₁.wbtw.mem_affineSpan
    rw [AffineSubspace.le_def'] at hle
    exact hle _ h₁'
  have h₁i := h₁.mem_image_Ioo
  have h₂i := h₂.mem_image_Ioo
  rw [Set.mem_image] at h₁i h₂i
  rcases h₁i with ⟨r₁, ⟨hr₁0, hr₁1⟩, rfl⟩
  rcases h₂i with ⟨r₂, ⟨hr₂0, hr₂1⟩, rfl⟩
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype hp with ⟨w, hw, rfl⟩
  have h₁s :=
    sign_eq_of_affineCombination_mem_affineSpan_single_lineMap t.independent hw (Finset.mem_univ _)
      (Finset.mem_univ _) (Finset.mem_univ _) h₁₂ h₁₃ h₂₃ hr₁0 hr₁1 h₁'
  have h₂s :=
    sign_eq_of_affineCombination_mem_affineSpan_single_lineMap t.independent hw (Finset.mem_univ _)
      (Finset.mem_univ _) (Finset.mem_univ _) h₁₂.symm h₂₃ h₁₃ hr₂0 hr₂1 h₂'
  rw [← Finset.univ.affineCombination_piSingle R t.points
      (Finset.mem_univ i₁),
    ← Finset.univ.affineCombination_affineCombinationLineMapWeights t.points (Finset.mem_univ _)
      (Finset.mem_univ _)] at h₁' ⊢
  refine
    Sbtw.affineCombination_of_mem_affineSpan_pair t.independent hw (Fintype.sum_pi_single' _ _)
      (Finset.univ.sum_affineCombinationLineMapWeights (Finset.mem_univ _) (Finset.mem_univ _) _)
      h₁' (Finset.mem_univ i₁) ?_
  rw [Pi.single_eq_same,
    Finset.affineCombinationLineMapWeights_apply_of_ne h₁₂ h₁₃, sbtw_one_zero_iff]
  have hs : ∀ i : Fin 3, SignType.sign (w i) = SignType.sign (w i₃) := by
    intro i
    rcases h3 i with (rfl | rfl | rfl)
    · exact h₂s
    · exact h₁s
    · rfl
  have hss : SignType.sign (∑ i, w i) = 1 := by simp [hw]
  have hs' := sign_sum Finset.univ_nonempty (SignType.sign (w i₃)) fun i _ => hs i
  rw [hs'] at hss
  simp_rw [hss, sign_eq_one_iff] at hs
  refine ⟨hs i₁, ?_⟩
  rw [hu] at hw
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] at hw
  · by_contra hle
    rw [not_lt] at hle
    exact (hle.trans_lt (lt_add_of_pos_right _ (Left.add_pos (hs i₂) (hs i₃)))).ne' hw
  · simpa using h₂₃
  · simpa [not_or] using ⟨h₁₂, h₁₃⟩

end LinearOrderedRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P] {x y z : P}
variable {R}

/-
**wbtw_iff_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：wbtw_iff_of_le {x y z : R} (hxz : x <= z) : Wbtw R x y z ↔ x <= y ∧ y <= z
参数：hxz : x <= z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `wbtw_self_iff`：wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 40 条，此处仅展示前 30 条）
-/
lemma wbtw_iff_of_le {x y z : R} (hxz : x ≤ z) : Wbtw R x y z ↔ x ≤ y ∧ y ≤ z := by
  cases hxz.eq_or_lt with
  | inl hxz =>
    subst hxz
    rw [← le_antisymm_iff, wbtw_self_iff, eq_comm]
  | inr hxz =>
    have hxz' : 0 < z - x := sub_pos.mpr hxz
    let r := (y - x) / (z - x)
    have hy : y = r * (z - x) + x := by simp [r, hxz'.ne']
    simp [hy, wbtw_mul_sub_add_iff, mul_nonneg_iff_of_pos_right hxz', ← le_sub_iff_add_le,
      mul_le_iff_le_one_left hxz', hxz.ne]
/-
**Wbtw.of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Wbtw.of_le_of_le {x y z : R} (hxy : x <= y) (hyz : y <= z) : Wbtw R x y z
参数：hxy : x <= y；hyz : y <= z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `wbtw_iff_of_le`：wbtw_iff_of_le {x y z : R} (hxz : x <= z) : Wbtw R x y z
 ↔ x <= y ∧ y <= z
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma Wbtw.of_le_of_le {x y z : R} (hxy : x ≤ y) (hyz : y ≤ z) : Wbtw R x y z :=
  (wbtw_iff_of_le (hxy.trans hyz)).mpr ⟨hxy, hyz⟩
/-
**Sbtw.of_lt_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Sbtw.of_lt_of_lt {x y z : R} (hxy : x < y) (hyz : y < z) : Sbtw R x y z
参数：hxy : x < y；hyz : y < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Wbtw.of_le_of_le`：Wbtw.of_le_of_le {x y z : R} (hxy : x <= y) (hyz : y <
= z) : Wbtw R x y z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma Sbtw.of_lt_of_lt {x y z : R} (hxy : x < y) (hyz : y < z) : Sbtw R x y z :=
  ⟨.of_le_of_le hxy.le hyz.le, hxy.ne', hyz.ne⟩

set_option backward.isDefEq.respectTransparency false in
/-
**wbtw_iff_left_eq_or_right_mem_image_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_iff_left_eq_or_right_mem_image_Ici {x y z : P} : Wbtw R x y z ↔ x = y
 ∨ z in lineMap x y '' Set.Ici (1 : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_le_inv₀`：one_le_inv₀ (ha : 0 < a) : 1 <= a⁻¹ ↔ a <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `wbtw_self_left`：wbtw_self_left (x y : P) : Wbtw R x x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
（共 35 条，此处仅展示前 30 条）
-/
theorem wbtw_iff_left_eq_or_right_mem_image_Ici {x y z : P} :
    Wbtw R x y z ↔ x = y ∨ z ∈ lineMap x y '' Set.Ici (1 : R) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rcases hr0.lt_or_eq with (hr0' | rfl)
    · rw [Set.mem_image]
      refine .inr ⟨r⁻¹, (one_le_inv₀ hr0').2 hr1, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ hr0'.ne', one_smul, vsub_vadd]
    · simp
  · rcases h with (rfl | ⟨r, ⟨hr, rfl⟩⟩)
    · exact wbtw_self_left _ _ _
    · rw [Set.mem_Ici] at hr
      refine ⟨r⁻¹, ⟨inv_nonneg.2 (zero_le_one.trans hr), inv_le_one_of_one_le₀ hr⟩, ?_⟩
      simp only [lineMap_apply, smul_smul, vadd_vsub]
      rw [inv_mul_cancel₀ (one_pos.trans_le hr).ne', one_smul, vsub_vadd]

set_option backward.isDefEq.respectTransparency false in
/-
**Wbtw.right_mem_image_Ici_of_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.right_mem_image_Ici_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne : 
x != y) : z in lineMap x y '' Set.Ici (1 : R)
参数：h : Wbtw R x y z；hne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wbtw_iff_left_eq_or_right_mem_image_Ici`：wbtw_iff_left_eq_or_right_mem_i
mage_Ici {x y z : P} : Wbtw R x y z ↔ x = y ∨ z in lineMap x y '' Set.Ici (1 : R
)
-/
theorem Wbtw.right_mem_image_Ici_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne : x ≠ y) :
    z ∈ lineMap x y '' Set.Ici (1 : R) :=
  (wbtw_iff_left_eq_or_right_mem_image_Ici.1 h).resolve_left hne
/-
**Wbtw.right_mem_affineSpan_of_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.right_mem_affineSpan_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne :
 x != y) : z in line[R, x, y]
参数：h : Wbtw R x y z；hne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.right_mem_image_Ici_of_left_ne`：Wbtw.right_mem_image_Ici_of_left_ne
 {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in lineMap x y '' Set.Ici (1 
: R)
· 使用定理 `AffineMap.lineMap_mem_affineSpan_pair`：AffineMap.lineMap_mem_affineSpan_
pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂]
-/
theorem Wbtw.right_mem_affineSpan_of_left_ne {x y z : P} (h : Wbtw R x y z) (hne : x ≠ y) :
    z ∈ line[R, x, y] := by
  rcases h.right_mem_image_Ici_of_left_ne hne with ⟨r, ⟨-, rfl⟩⟩
  exact lineMap_mem_affineSpan_pair _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**sbtw_iff_left_ne_and_right_mem_image_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_iff_left_ne_and_right_mem_image_Ioi {x y z : P} : Sbtw R x y z ↔ x !=
 y ∧ z in lineMap x y '' Set.Ioi (1 : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Wbtw.right_mem_image_Ici_of_left_ne`：Wbtw.right_mem_image_Ici_of_left_ne
 {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in lineMap x y '' Set.Ici (1 
: R)
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `wbtw_iff_left_eq_or_right_mem_image_Ici`：wbtw_iff_left_eq_or_right_mem_i
mage_Ici {x y z : P} : Wbtw R x y z ↔ x = y ∨ z in lineMap x y '' Set.Ici (1 : R
)
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem sbtw_iff_left_ne_and_right_mem_image_Ioi {x y z : P} :
    Sbtw R x y z ↔ x ≠ y ∧ z ∈ lineMap x y '' Set.Ioi (1 : R) := by
  refine ⟨fun h => ⟨h.left_ne, ?_⟩, fun h => ?_⟩
  · obtain ⟨r, ⟨hr, rfl⟩⟩ := h.wbtw.right_mem_image_Ici_of_left_ne h.left_ne
    rw [Set.mem_Ici] at hr
    rcases hr.lt_or_eq with (hrlt | rfl)
    · exact Set.mem_image_of_mem _ hrlt
    · simp at h
  · rcases h with ⟨hne, r, hr, rfl⟩
    rw [Set.mem_Ioi] at hr
    refine
      ⟨wbtw_iff_left_eq_or_right_mem_image_Ici.2
          (Or.inr (Set.mem_image_of_mem _ (Set.mem_of_mem_of_subset hr Set.Ioi_subset_Ici_self))),
        hne.symm, ?_⟩
    rw [lineMap_apply, ← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub]
    nth_rw 1 [← one_smul R (y -ᵥ x)]
    rw [← sub_smul, smul_ne_zero_iff, vsub_ne_zero, sub_ne_zero]
    exact ⟨hr.ne, hne.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Sbtw.right_mem_image_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.right_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) : z in lineMap x y
 '' Set.Ioi (1 : R)
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sbtw_iff_left_ne_and_right_mem_image_Ioi`：sbtw_iff_left_ne_and_right_mem
_image_Ioi {x y z : P} : Sbtw R x y z ↔ x != y ∧ z in lineMap x y '' Set.Ioi (1 
: R)
-/
theorem Sbtw.right_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) :
    z ∈ lineMap x y '' Set.Ioi (1 : R) :=
  (sbtw_iff_left_ne_and_right_mem_image_Ioi.1 h).2
/-
**Sbtw.right_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.right_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : z in line[R, x,
 y]
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.right_mem_affineSpan_of_left_ne`：Wbtw.right_mem_affineSpan_of_left_
ne {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in line[R, x, y]
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
-/
theorem Sbtw.right_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : z ∈ line[R, x, y] :=
  h.wbtw.right_mem_affineSpan_of_left_ne h.left_ne

set_option backward.isDefEq.respectTransparency false in
/-
**wbtw_iff_right_eq_or_left_mem_image_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_iff_right_eq_or_left_mem_image_Ici {x y z : P} : Wbtw R x y z ↔ z = y
 ∨ x in lineMap z y '' Set.Ici (1 : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `wbtw_iff_left_eq_or_right_mem_image_Ici`：wbtw_iff_left_eq_or_right_mem_i
mage_Ici {x y z : P} : Wbtw R x y z ↔ x = y ∨ z in lineMap x y '' Set.Ici (1 : R
)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wbtw_iff_right_eq_or_left_mem_image_Ici {x y z : P} :
    Wbtw R x y z ↔ z = y ∨ x ∈ lineMap z y '' Set.Ici (1 : R) := by
  rw [wbtw_comm, wbtw_iff_left_eq_or_right_mem_image_Ici]

set_option backward.isDefEq.respectTransparency false in
/-
**Wbtw.left_mem_image_Ici_of_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.left_mem_image_Ici_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne : 
z != y) : x in lineMap z y '' Set.Ici (1 : R)
参数：h : Wbtw R x y z；hne : z != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.right_mem_image_Ici_of_left_ne`：Wbtw.right_mem_image_Ici_of_left_ne
 {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in lineMap x y '' Set.Ici (1 
: R)
· 使用定理 `Wbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Wbtw.left_mem_image_Ici_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne : z ≠ y) :
    x ∈ lineMap z y '' Set.Ici (1 : R) :=
  h.symm.right_mem_image_Ici_of_left_ne hne
/-
**Wbtw.left_mem_affineSpan_of_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.left_mem_affineSpan_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne :
 z != y) : x in line[R, z, y]
参数：h : Wbtw R x y z；hne : z != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.right_mem_affineSpan_of_left_ne`：Wbtw.right_mem_affineSpan_of_left_
ne {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in line[R, x, y]
· 使用定理 `Wbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Wbtw.left_mem_affineSpan_of_right_ne {x y z : P} (h : Wbtw R x y z) (hne : z ≠ y) :
    x ∈ line[R, z, y] :=
  h.symm.right_mem_affineSpan_of_left_ne hne

set_option backward.isDefEq.respectTransparency false in
/-
**sbtw_iff_right_ne_and_left_mem_image_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_iff_right_ne_and_left_mem_image_Ioi {x y z : P} : Sbtw R x y z ↔ z !=
 y ∧ x in lineMap z y '' Set.Ioi (1 : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sbtw_comm`：sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `sbtw_iff_left_ne_and_right_mem_image_Ioi`：sbtw_iff_left_ne_and_right_mem
_image_Ioi {x y z : P} : Sbtw R x y z ↔ x != y ∧ z in lineMap x y '' Set.Ioi (1 
: R)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sbtw_iff_right_ne_and_left_mem_image_Ioi {x y z : P} :
    Sbtw R x y z ↔ z ≠ y ∧ x ∈ lineMap z y '' Set.Ioi (1 : R) := by
  rw [sbtw_comm, sbtw_iff_left_ne_and_right_mem_image_Ioi]

set_option backward.isDefEq.respectTransparency false in
/-
**Sbtw.left_mem_image_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.left_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) : x in lineMap z y 
'' Set.Ioi (1 : R)
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.right_mem_image_Ioi`：Sbtw.right_mem_image_Ioi {x y z : P} (h : Sbtw
 R x y z) : z in lineMap x y '' Set.Ioi (1 : R)
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Sbtw.left_mem_image_Ioi {x y z : P} (h : Sbtw R x y z) :
    x ∈ lineMap z y '' Set.Ioi (1 : R) :=
  h.symm.right_mem_image_Ioi
/-
**Sbtw.left_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.left_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : x in line[R, z, 
y]
参数：h : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.right_mem_affineSpan`：Sbtw.right_mem_affineSpan {x y z : P} (h : Sb
tw R x y z) : z in line[R, x, y]
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Sbtw.left_mem_affineSpan {x y z : P} (h : Sbtw R x y z) : x ∈ line[R, z, y] :=
  h.symm.right_mem_affineSpan

omit [IsStrictOrderedRing R] in
/-
**AffineSubspace.right_mem_of_wbtw** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineSubspace.right_mem_of_wbtw {s : AffineSubspace R P} (hxyz : Wbtw R x
 y z) (hx : x in s) (hy : y in s) (hxy : x != y) : z in s
参数：hxyz : Wbtw R x y z；hx : x in s；hy : y in s；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_lineMap_right`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : 
Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V1]   [inst_2 : _root_.Module k
 V1] [inst_3 : AddTor…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
-/
lemma AffineSubspace.right_mem_of_wbtw {s : AffineSubspace R P} (hxyz : Wbtw R x y z) (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) : z ∈ s := by
  obtain ⟨ε, -, rfl⟩ := hxyz
  have hε : ε ≠ 0 := by rintro rfl; simp at hxy
  simpa [hε] using lineMap_mem ε⁻¹ hx hy
/-
**wbtw_smul_vadd_smul_vadd_of_nonneg_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ 
: 0 <= r₁) (hr₂ : r₁ <= r₂) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
参数：x : P；v : V；hr₁ : 0 <= r₁；hr₂ : r₁ <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁)
    (hr₂ : r₁ ≤ r₂) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  refine ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le₀ hr₂ (hr₁.trans hr₂)⟩, ?_⟩
  by_cases h : r₁ = 0; · simp [h]
  simp [lineMap_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).ne.symm]
/-
**wbtw_or_wbtw_smul_vadd_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_or_wbtw_smul_vadd_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r
₁) (hr₂ : 0 <= r₂) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ 
x) (r₁ • v +ᵥ x)
参数：x : P；v : V；hr₁ : 0 <= r₁；hr₂ : 0 <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le`：wbtw_smul_vadd_smul_vadd_of_no
nneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : r₁ <= r₂) : Wbtw R
 x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
-/
theorem wbtw_or_wbtw_smul_vadd_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h)
/-
**wbtw_smul_vadd_smul_vadd_of_nonpos_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_smul_vadd_smul_vadd_of_nonpos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ 
: r₁ <= 0) (hr₂ : r₂ <= r₁) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
参数：x : P；v : V；hr₁ : r₁ <= 0；hr₂ : r₂ <= r₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le`：wbtw_smul_vadd_smul_vadd_of_no
nneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : r₁ <= r₂) : Wbtw R
 x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0)
    (hr₂ : r₂ ≤ r₁) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_neg_iff.2 hr₂) using
    1 <;>
    rw [neg_smul_neg]
/-
**wbtw_or_wbtw_smul_vadd_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_or_wbtw_smul_vadd_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 
0) (hr₂ : r₂ <= 0) : Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ 
x) (r₁ • v +ᵥ x)
参数：x : P；v : V；hr₁ : r₁ <= 0；hr₂ : r₂ <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonpos_of_le`：wbtw_smul_vadd_smul_vadd_of_no
npos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : r₂ <= r₁) : Wbtw R
 x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
-/
theorem wbtw_or_wbtw_smul_vadd_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0) (hr₂ : r₂ ≤ 0) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h)
/-
**wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (
hr₁ : r₁ <= 0) (hr₂ : 0 <= r₂) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x)
参数：x : P；v : V；hr₁ : r₁ <= 0；hr₂ : 0 <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le`：wbtw_smul_vadd_smul_vadd_of_no
nneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : r₁ <= r₂) : Wbtw R
 x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `neg_le_sub_iff_le_add`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : 
LE α] [AddLeftMono α] {a b c : α}, -b ≤ a - c ↔ c ≤ a + b
· 使用定理 `le_add_iff_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddRightMono α] [AddRightReflectLE α] (a : α) {b : α},   a ≤ b + a ↔ 0
 ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0)
    (hr₂ : 0 ≤ r₂) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  convert!
    wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (Left.nonneg_neg_iff.2 hr₁)
      (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using
    1 <;>
    simp [sub_smul, ← add_vadd]
/-
**wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (
hr₁ : 0 <= r₁) (hr₂ : r₂ <= 0) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x)
参数：x : P；v : V；hr₁ : 0 <= r₁；hr₂ : r₂ <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg`：wbtw_smul_vadd_smul_vadd_o
f_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : 0 <= r₂) :
 Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ…
-/
theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁)
    (hr₂ : r₂ ≤ 0) : Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  rw [wbtw_comm]
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁
/-
**Wbtw.trans_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y
) : Wbtw R x y z
参数：h₁ : Wbtw R w y z；h₂ : Wbtw R w x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
（共 83 条，此处仅展示前 30 条）
-/
theorem Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) :
    Wbtw R x y z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine
    ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
      ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2))
          (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2)), div_le_one_of_le₀
            (sub_le_sub_right ht₁.2 _) (sub_nonneg.2 (mul_le_one₀ ht₂.2 ht₁.1 ht₁.2))⟩,
      ?_⟩
  simp only [lineMap_apply, smul_smul, ← add_vadd, vsub_vadd_eq_vsub_sub, smul_sub, ← sub_smul,
    ← add_smul, vadd_vsub, vadd_right_cancel_iff, div_mul_eq_mul_div, div_sub_div_same]
  nth_rw 1 [← mul_one (t₁ - t₂ * t₁)]
  rw [← mul_sub, mul_div_assoc]
  by_cases h : 1 - t₂ * t₁ = 0
  · rw [sub_eq_zero, eq_comm] at h
    rw [h]
    suffices t₁ = 1 by simp [this]
    exact
      eq_of_le_of_not_lt ht₁.2 fun ht₁lt =>
        (mul_lt_one_of_nonneg_of_lt_one_right ht₂.2 ht₁.1 ht₁lt).ne h
  · rw [div_self h]
    ring_nf
/-
**Wbtw.trans_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_right_left {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z
) : Wbtw R w x y
参数：h₁ : Wbtw R w x z；h₂ : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Wbtw.trans_left_right`：Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R 
w y z) (h₂ : Wbtw R w x y) : Wbtw R x y z
-/
theorem Wbtw.trans_right_left {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) :
    Wbtw R w x y := by
  rw [wbtw_comm] at *
  exact h₁.trans_left_right h₂
/-
**Sbtw.trans_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_left_right {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y
) : Sbtw R x y z
参数：h₁ : Sbtw R w y z；h₂ : Sbtw R w x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_left_right`：Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R 
w y z) (h₂ : Wbtw R w x y) : Wbtw R x y z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.right_ne`：Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z != y
· 使用定理 `Sbtw.ne_right`：Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y != z
-/
theorem Sbtw.trans_left_right {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) :
    Sbtw R x y z :=
  ⟨h₁.wbtw.trans_left_right h₂.wbtw, h₂.right_ne, h₁.ne_right⟩
/-
**Sbtw.trans_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_right_left {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z
) : Sbtw R w x y
参数：h₁ : Sbtw R w x z；h₂ : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_right_left`：Wbtw.trans_right_left {w x y z : P} (h₁ : Wbtw R 
w x z) (h₂ : Wbtw R x y z) : Wbtw R w x y
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.ne_left`：Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
-/
theorem Sbtw.trans_right_left {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) :
    Sbtw R w x y :=
  ⟨h₁.wbtw.trans_right_left h₂.wbtw, h₁.ne_left, h₂.left_ne⟩
/-
**Wbtw.trans_expand_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_expand_left {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y 
z) (h_ne : x != y) : Wbtw R w x z
参数：h₁ : Wbtw R w x y；h₂ : Wbtw R x y z；h_ne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 88 条，此处仅展示前 30 条）
-/
theorem Wbtw.trans_expand_left {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
    (h_ne : x ≠ y) : Wbtw R w x z := by
  rcases h₁ with ⟨t₁, ht₁, hx⟩
  rcases h₂ with ⟨t₂, ht₂, hy⟩
  refine ⟨t₁ * t₂ / (1 - t₁ + t₁ * t₂), ?_, ?_⟩
  · constructor
    · apply div_nonneg (mul_nonneg ht₁.1 ht₂.1)
      nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    · apply div_le_one_of_le₀
      · grind
      · nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
  have h_denom : 1 - t₁ + t₁ * t₂ ≠ 0 := by
    contrapose h_ne
    have h1 : t₁ = 1 := by nlinarith [ht₁.1, ht₁.2, ht₂.1, ht₂.2]
    rw [← hx, h1, lineMap_apply_one]
  rw [← hy, lineMap_apply, lineMap_apply, eq_comm, eq_vadd_iff_vsub_eq] at hx
  rw [lineMap_apply, eq_comm, eq_vadd_iff_vsub_eq, div_eq_mul_inv, mul_comm, mul_smul,
    eq_inv_smul_iff₀ h_denom, add_smul, sub_smul, one_smul]
  nth_rw 1 [hx]
  rw [← smul_sub, mul_smul, mul_smul, vsub_sub_vsub_cancel_right, vadd_vsub, ← smul_assoc,
    ← smul_assoc, ← smul_assoc, ← smul_add, vsub_add_vsub_cancel]
/-
**Wbtw.trans_expand_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.trans_expand_right {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y
 z) (h_ne : x != y) : Wbtw R w y z
参数：h₁ : Wbtw R w x y；h₂ : Wbtw R x y z；h_ne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_right`：Wbtw.trans_right {w x y z : P} (h₁ : Wbtw R w x z) (h₂
 : Wbtw R x y z) : Wbtw R w y z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Wbtw.trans_expand_left`：Wbtw.trans_expand_left {w x y z : P} (h₁ : Wbtw 
R w x y) (h₂ : Wbtw R x y z) (h_ne : x != y) : Wbtw R w x z
-/
theorem Wbtw.trans_expand_right {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z)
    (h_ne : x ≠ y) : Wbtw R w y z := Wbtw.trans_right (h₁.trans_expand_left h₂ h_ne) h₂
/-
**Sbtw.trans_expand_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_expand_left {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y 
z) : Sbtw R w x z
参数：h₁ : Sbtw R w x y；h₂ : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.trans_expand_left`：Wbtw.trans_expand_left {w x y z : P} (h₁ : Wbtw 
R w x y) (h₂ : Wbtw R x y z) (h_ne : x != y) : Wbtw R w x z
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Sbtw.trans_expand_left {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z) :
    Sbtw R w x z :=
  ⟨Wbtw.trans_expand_left h₁.wbtw h₂.wbtw h₂.left_ne, h₁.left_ne.symm, h₂.left_ne_right⟩
/-
**Sbtw.trans_expand_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.trans_expand_right {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y
 z) : Sbtw R w y z
参数：h₁ : Sbtw R w x y；h₂ : Sbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.trans_right`：Sbtw.trans_right (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y 
z) : Sbtw R w y z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Sbtw.trans_expand_left`：Sbtw.trans_expand_left {w x y z : P} (h₁ : Sbtw 
R w x y) (h₂ : Sbtw R x y z) : Sbtw R w x z
-/
theorem Sbtw.trans_expand_right {w x y z : P} (h₁ : Sbtw R w x y) (h₂ : Sbtw R x y z) :
    Sbtw R w y z := Sbtw.trans_right (h₁.trans_expand_left h₂) h₂

omit [IsStrictOrderedRing R] in
/-
**Wbtw.collinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinear R ({x, y, z} : S
et P)
参数：h : Wbtw R x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_insert_of_mem_affineSpan_pair`：collinear_insert_of_mem_affineS
pan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) : Collinear k ({p₁, p₂, p₃} 
: Set P)
· 使用定理 `Wbtw.mem_affineSpan`：Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) 
: y in line[R, x, z]
-/
theorem Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinear R ({x, y, z} : Set P) := by
  have : {y, x, z} = {x, y, z} := Set.insert_comm y x {z}
  simpa [this] using collinear_insert_of_mem_affineSpan_pair (mem_affineSpan h)
/-
**Collinear.wbtw_or_wbtw_or_wbtw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.wbtw_or_wbtw_or_wbtw {x y z : P} (h : Collinear R ({x, y, z} : S
et P)) : Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y
参数：h : Collinear R ({x, y, z} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_of_mem`：collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ 
in s) : Collinear k s ↔ exists v : V, forall p in s, exists r : k, p = r • v +ᵥ 
p₀
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `wbtw_comm`：wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `wbtw_or_wbtw_smul_vadd_of_nonpos`：wbtw_or_wbtw_smul_vadd_of_nonpos (x : 
P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : r₂ <= 0) : Wbtw R x (r₁ • v +ᵥ x) 
(r₂ • v +ᵥ x) ∨ Wbtw R…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos`：wbtw_smul_vadd_smul_vadd_o
f_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : r₂ <= 0) :
 Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ…
· 使用定理 `wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg`：wbtw_smul_vadd_smul_vadd_o
f_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ <= 0) (hr₂ : 0 <= r₂) :
 Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ…
· 使用定理 `wbtw_or_wbtw_smul_vadd_of_nonneg`：wbtw_or_wbtw_smul_vadd_of_nonneg (x : 
P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂) : Wbtw R x (r₁ • v +ᵥ x) 
(r₂ • v +ᵥ x) ∨ Wbtw R…
-/
theorem Collinear.wbtw_or_wbtw_or_wbtw {x y z : P} (h : Collinear R ({x, y, z} : Set P)) :
    Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  rcases h with ⟨v, h⟩
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hy := h y (Or.inr (Or.inl rfl))
  have hz := h z (Or.inr (Or.inr rfl))
  rcases hy with ⟨ty, rfl⟩
  rcases hz with ⟨tz, rfl⟩
  rcases lt_trichotomy ty 0 with (hy0 | rfl | hy0)
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · rw [wbtw_comm (z := x)]
      rw [← or_assoc]
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0.le hz0.le)
    · simp
    · exact Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos _ _ hz0.le hy0.le))
  · simp
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · refine Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg _ _ hz0.le hy0.le))
    · simp
    · rw [wbtw_comm (z := x)]
      rw [← or_assoc]
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0.le hz0.le)
/-
**wbtw_iff_sameRay_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_iff_sameRay_vsub {x y z : P} : Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -
ᵥ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wbtw_vsub_const_iff`：wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x
 -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wbtw_iff_sameRay_vsub {x y z : P} : Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -ᵥ y) := by
  simp [← wbtw_vsub_const_iff x, ← mem_segment_iff_wbtw, mem_segment_iff_sameRay]
/-
**wbtw_total_of_sameRay_vsub_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：wbtw_total_of_sameRay_vsub_left {x y z : P} (h : SameRay R (y -ᵥ x) (z -ᵥ 
x)) : Wbtw R x y z ∨ Wbtw R x z y
参数：h : SameRay R (y -ᵥ x) (z -ᵥ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 57 条，此处仅展示前 30 条）
-/
lemma wbtw_total_of_sameRay_vsub_left {x y z : P} (h : SameRay R (y -ᵥ x) (z -ᵥ x)) :
    Wbtw R x y z ∨ Wbtw R x z y := by
  rcases h with (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · simp_all
  · simp_all
  wlog hr : r₂ ≤ r₁ generalizing r₁ r₂ y z
  · rw [or_comm]
    apply this r₂ r₁ hr₂ hr₁ h.symm (Std.le_of_not_ge hr)
  left
  refine ⟨r₂ / r₁, ⟨div_nonneg hr₂.le hr₁.le, div_le_one_of_le₀ hr hr₁.le⟩, ?_⟩
  have h' : y = r₁⁻¹ • r₂ • (z -ᵥ x) +ᵥ x := by simp [← h, hr₁.ne']
  simp only [lineMap_apply, h', vadd_vsub_assoc, smul_smul, eq_vadd_iff_vsub_eq, vsub_self,
    add_zero]
  ring_nf

/-- If `T` is an affine independent family of points,
then any 3 distinct points form a triangle. -/
/-
**AffineIndependent.not_wbtw_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.not_wbtw_of_injective {ι} (i j k : ι) (h : Function.Inje
ctive ![i, j, k]) {T : ι -> P} (hT : AffineIndependent R T) : ¬ Wbtw R (T i) (T 
j) (T k)
参数：i j k : ι；h : Function.Injective ![i, j, k]；hT : AffineIndependent R T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Wbtw.collinear`：Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinea
r R ({x, y, z} : Set P)
· 使用定理 `Wbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `affineIndependent_iff_not_collinear`：affineIndependent_iff_not_collinear
 {p : Fin 3 -> P} : AffineIndependent k p ↔ ¬Collinear k (Set.range p)

--- 原说明 ---
If `T` is an affine independent family of points,
then any 3 distinct points form a triangle.
-/
theorem AffineIndependent.not_wbtw_of_injective {ι} (i j k : ι)
    (h : Function.Injective ![i, j, k]) {T : ι → P} (hT : AffineIndependent R T) :
    ¬ Wbtw R (T i) (T j) (T k) := by
  replace hT := hT.comp_embedding ⟨_, h⟩
  rw [affineIndependent_iff_not_collinear] at hT
  contrapose hT
  simp [Set.range_comp, Set.image_insert_eq, hT.symm.collinear]

variable (R)
/-
**wbtw_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_pointReflection (x y : P) : Wbtw R y x (pointReflection R x y)
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `AffineEquiv.pointReflection_apply`：pointReflection_apply (x y : P₁) : po
intReflection k x y = (x -ᵥ y) +ᵥ x
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wbtw_pointReflection (x y : P) : Wbtw R y x (pointReflection R x y) := by
  refine ⟨2⁻¹, ⟨by simp, by norm_num⟩, ?_⟩
  rw [lineMap_apply, pointReflection_apply, vadd_vsub_assoc, ← two_smul R (x -ᵥ y)]
  simp
/-
**sbtw_pointReflection_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_pointReflection_of_ne {x y : P} (h : x != y) : Sbtw R y x (pointRefle
ction R x y)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wbtw_pointReflection`：wbtw_pointReflection (x y : P) : Wbtw R y x (point
Reflection R x y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.pointReflection_self`：pointReflection_self (x : P₁) : pointR
eflection k x x = x
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `AffineEquiv.pointReflection_involutive`：pointReflection_involutive (x : 
P₁) : Involutive (pointReflection k x : P₁ -> P₁)
-/
theorem sbtw_pointReflection_of_ne {x y : P} (h : x ≠ y) : Sbtw R y x (pointReflection R x y) := by
  refine ⟨wbtw_pointReflection _ _ _, h, ?_⟩
  nth_rw 1 [← pointReflection_self R x]
  exact (pointReflection_involutive R x).injective.ne h
/-
**wbtw_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wbtw_midpoint (x y : P) : Wbtw R x (midpoint R x y) y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineEquiv.pointReflection_midpoint_left`：AffineEquiv.pointReflection_m
idpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y
· 使用定理 `wbtw_pointReflection`：wbtw_pointReflection (x y : P) : Wbtw R y x (point
Reflection R x y)
-/
theorem wbtw_midpoint (x y : P) : Wbtw R x (midpoint R x y) y := by
  convert! wbtw_pointReflection R (midpoint R x y) x
  rw [pointReflection_midpoint_left]
/-
**sbtw_midpoint_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R x (midpoint R x y) y
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.pointReflection_midpoint_left`：AffineEquiv.pointReflection_m
idpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y
· 使用定理 `sbtw_pointReflection_of_ne`：sbtw_pointReflection_of_ne {x y : P} (h : x 
!= y) : Sbtw R y x (pointReflection R x y)
-/
theorem sbtw_midpoint_of_ne {x y : P} (h : x ≠ y) : Sbtw R x (midpoint R x y) y := by
  have h : midpoint R x y ≠ x := by simp [h]
  convert! sbtw_pointReflection_of_ne R h
  rw [pointReflection_midpoint_left]

end LinearOrderedField

