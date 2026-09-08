/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Ray

import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `openSegment 𝕜 x y`: Open segment joining `x` and `y`.

## Notation

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in scope `Convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `openSegment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopenSegment`/`convex.Ico`/`convex.Ioc`?
-/

@[expose] public section

variable {𝕜 E F G ι : Type*} {M : ι → Type*}

open Function Module Set
open scoped Pointwise Convex

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section SMul

variable (𝕜) [SMul 𝕜 E] {s : Set E} {x y : E}

/-- Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace. -/
/-
**segment** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：segment (x y : E) : Set E
参数：x y : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespac
e.
-/
def segment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z }

/-- Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
/-
**openSegment** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：openSegment (x y : E) : Set E
参数：x y : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of b
eing `∅` when
the base semiring has some element between `0` and `1`.
-/
def openSegment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }

@[inherit_doc] scoped[Convex] notation (priority := high) "[" x " -[" 𝕜 "] " y "]" => segment 𝕜 x y
/-
**segment_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • 
y) '' Icc (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem segment_eq_image₂ (x y : E) :
    [x -[𝕜] y] =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [segment, image, Prod.exists, mem_ofPred_eq, and_assoc]
/-
**openSegment_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_image (x y : E) : openSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ)
 • x + θ • y) '' Ioo (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `AddGroup.addRightReflectLE_of_addRightMono`：∀ {N : Type u_2} [inst : Add
Group N] [inst_1 : LE N] [AddRightMono N], AddRightReflectLE N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem openSegment_eq_image₂ (x y : E) :
    openSegment 𝕜 x y =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [openSegment, image, Prod.exists, mem_ofPred_eq, and_assoc]
/-
**segment_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩
/-
**openSegment_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_symm (x y : E) : openSegment 𝕜 x y = openSegment 𝕜 y x
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem openSegment_symm (x y : E) : openSegment 𝕜 x y = openSegment 𝕜 y x :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩
/-
**openSegment_subset_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_segment (x y : E) : openSegment 𝕜 x y subseteq [x -[𝕜] 
y]
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem openSegment_subset_segment (x y : E) : openSegment 𝕜 x y ⊆ [x -[𝕜] y] :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩
/-
**segment_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_iff : [x -[𝕜] y] subseteq s ↔ forall a b : 𝕜, 0 <= a -> 0 <
= b -> a + b = 1 -> a • x + b • y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem segment_subset_iff :
    [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩
/-
**openSegment_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_iff : openSegment 𝕜 x y subseteq s ↔ forall a b : 𝕜, 0 
< a -> 0 < b -> a + b = 1 -> a • x + b • y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem openSegment_subset_iff :
    openSegment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

end SMul

open Convex

section MulActionWithZero

variable (𝕜)
variable [ZeroLEOneClass 𝕜] [MulActionWithZero 𝕜 E]

/-
**left_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_mem_segment (x y : E) : x in [x -[𝕜] y]
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
  ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩
/-
**right_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_mem_segment (x y : E) : y in [x -[𝕜] y]
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_mem_segment`：left_mem_segment (x y : E) : x in [x -[𝕜] y]
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
-/
theorem right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
  segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end MulActionWithZero

section Module

variable (𝕜)
variable [ZeroLEOneClass 𝕜] [Module 𝕜 E] {s : Set E} {x y z : E}

@[simp]
/-
**segment_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_same (x : E) : [x -[𝕜] x] = {x}
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `left_mem_segment`：left_mem_segment (x y : E) : x in [x -[𝕜] y]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem segment_same (x : E) : [x -[𝕜] x] = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩
/-
**insert_endpoints_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：insert_endpoints_openSegment (x y : E) : insert x (insert y (openSegment 𝕜
 x y)) = [x -[𝕜] y]
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
-/
theorem insert_endpoints_openSegment (x y : E) :
    insert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y] := by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_lt.imp ?_ fun hb' => ha.eq_or_lt.imp ?_ fun ha' => ?_
  · rintro rfl
    rw [← add_zero a, hab, one_smul, zero_smul, add_zero]
  · rintro rfl
    rw [← zero_add b, hab, one_smul, zero_smul, zero_add]
  · exact ⟨a, b, ha', hb', hab, rfl⟩

variable {𝕜}
/-
**mem_openSegment_of_ne_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_of_ne_left_right (hx : x != z) (hy : y != z) (hz : z in [x
 -[𝕜] y]) : z in openSegment 𝕜 x y
参数：hx : x != z；hy : y != z；hz : z in [x -[𝕜] y]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `insert_endpoints_openSegment`：insert_endpoints_openSegment (x y : E) : i
nsert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y]
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem mem_openSegment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) :
    z ∈ openSegment 𝕜 x y := by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm
/-
**openSegment_subset_iff_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_iff_segment_subset (hx : x in s) (hy : y in s) : openSe
gment 𝕜 x y subseteq s ↔ [x -[𝕜] y] subseteq s
参数：hx : x in s；hy : y in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem openSegment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s := by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and]

section lift

variable (R : Type*) [Semiring R] [PartialOrder R] [Module R E]
variable [Module R 𝕜] [IsScalarTower R 𝕜 E]

/-
**segment.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment.lift [SMulPosMono R 𝕜] (x y : E) : segment R x y subseteq segment 
𝕜 x y
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem segment.lift [SMulPosMono R 𝕜] (x y : E) : segment R x y ⊆ segment 𝕜 x y := by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one
/-
**openSegment.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment.lift [Nontrivial 𝕜] [SMulPosStrictMono R 𝕜] (x y : E) : openSe
gment R x y subseteq openSegment 𝕜 x y
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem openSegment.lift [Nontrivial 𝕜] [SMulPosStrictMono R 𝕜] (x y : E) :
    openSegment R x y ⊆ openSegment 𝕜 x y := by
  rintro z ⟨a, b, ha, hb, hab, hxy⟩
  refine ⟨_, _, ?_, ?_, by simpa [add_smul] using congr($(hab) • (1 : 𝕜)), by simpa⟩
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_lt_smul_of_pos_right ‹_› zero_lt_one

end lift

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F]

section DenselyOrdered

variable [ZeroLEOneClass 𝕜] [Nontrivial 𝕜] [DenselyOrdered 𝕜]

@[simp]
/-
**openSegment_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_same (x : E) : openSegment 𝕜 x x = {x}
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DenselyOrdered.dense`：∀ {α : Type u_5} {inst : LT α} [self : DenselyOrde
red α] (a₁ a₂ : α), a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `AddGroup.addRightReflectLE_of_addRightMono`：∀ {N : Type u_2} [inst : Add
Group N] [inst_1 : LE N] [AddRightMono N], AddRightReflectLE N
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem openSegment_same (x : E) : openSegment 𝕜 x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, ?_⟩
      rw [← add_smul, add_sub_cancel, one_smul, h]⟩

end DenselyOrdered

/-
**segment_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • 
y) '' Icc (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem segment_eq_image (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩
/-
**openSegment_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_image (x y : E) : openSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ)
 • x + θ • y) '' Ioo (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `AddGroup.addRightReflectLE_of_addRightMono`：∀ {N : Type u_2} [inst : Add
Group N] [inst_1 : LE N] [AddRightMono N], AddRightReflectLE N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem openSegment_eq_image (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩
/-
**segment_eq_image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) 
'' Icc (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `_private.Mathlib.Analysis.Convex.Segment.0.segment_eq_image'._abel_1_1`：
∀ (𝕜 : Type u_2) {E : Type u_1} [inst : Ring 𝕜] [inst_1 : AddCommGroup E] [inst_
2 : _root_.Module 𝕜 E] (x y : E)   (a : 𝕜), x + (a • y - a •…
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
-/
theorem segment_eq_image' (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert! segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel
/-
**openSegment_eq_image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_image' (x y : E) : openSegment 𝕜 x y = (fun θ : 𝕜 => x + θ 
• (y - x)) '' Ioo (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `_private.Mathlib.Analysis.Convex.Segment.0.openSegment_eq_image'._abel_1
_1`：∀ (𝕜 : Type u_2) {E : Type u_1} [inst : Ring 𝕜] [inst_1 : AddCommGroup E] [i
nst_2 : _root_.Module 𝕜 E] (x y : E)   (a : 𝕜), x + (a • y - a •…
· 使用定理 `openSegment_eq_image`：openSegment_eq_image (x y : E) : openSegment 𝕜 x y
 = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1
-/
theorem openSegment_eq_image' (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 := by
  convert! openSegment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel

set_option backward.isDefEq.respectTransparency false in
/-
**segment_eq_image_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y] = AffineMap.lineMap x y ''
 Icc (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
-/
theorem segment_eq_image_lineMap (x y : E) : [x -[𝕜] y] =
    AffineMap.lineMap x y '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**openSegment_eq_image_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_image_lineMap (x y : E) : openSegment 𝕜 x y = AffineMap.lin
eMap x y '' Ioo (0 : 𝕜) 1
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `openSegment_eq_image`：openSegment_eq_image (x y : E) : openSegment 𝕜 x y
 = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1
-/
theorem openSegment_eq_image_lineMap (x y : E) :
    openSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1 := by
  convert openSegment_eq_image 𝕜 x y
  exact AffineMap.lineMap_apply_module _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**lineMap_mem_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_mem_openSegment (a b : E) {t : 𝕜} (ht : t in Ioo 0 1) : AffineMap.
lineMap a b t in openSegment 𝕜 a b
参数：a b : E；ht : t in Ioo 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `openSegment_eq_image_lineMap`：openSegment_eq_image_lineMap (x y : E) : o
penSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1
-/
theorem lineMap_mem_openSegment (a b : E) {t : 𝕜} (ht : t ∈ Ioo 0 1) :
    AffineMap.lineMap a b t ∈ openSegment 𝕜 a b :=
  openSegment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

set_option backward.isDefEq.respectTransparency.types false in
/-
**lineMap_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_mem_segment (a b : E) {t : 𝕜} (ht : t in Icc 0 1) : AffineMap.line
Map a b t in [a -[𝕜] b]
参数：a b : E；ht : t in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
-/
theorem lineMap_mem_segment (a b : E) {t : 𝕜} (ht : t ∈ Icc 0 1) :
    AffineMap.lineMap a b t ∈ [a -[𝕜] b] :=
  segment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

@[simp]
/-
**image_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_segment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b
]
参数：f : E ->ᵃ[𝕜] F；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_segment (f : E →ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image_lineMap, mem_image, exists_exists_and_eq_and, AffineMap.apply_lineMap]

@[simp]
/-
**image_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' openSegment 𝕜 a b = op
enSegment 𝕜 (f a) (f b)
参数：f : E ->ᵃ[𝕜] F；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `openSegment_eq_image_lineMap`：openSegment_eq_image_lineMap (x y : E) : o
penSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_openSegment (f : E →ᵃ[𝕜] F) (a b : E) :
    f '' openSegment 𝕜 a b = openSegment 𝕜 (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [openSegment_eq_image_lineMap, mem_image, exists_exists_and_eq_and,
      AffineMap.apply_lineMap]

@[simp]
/-
**vadd_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vadd_segment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) : a +
ᵥ [b -[𝕜] c] = [a +ᵥ b -[𝕜] a +ᵥ c]
参数：a : G；b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_segment`：image_segment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b
] = [f a -[𝕜] f b]
· 使用定理 `VAddCommClass.vadd_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : VAdd M α} {inst_1 : VAdd N α} [self : VAddCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem vadd_segment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ [b -[𝕜] c] = [a +ᵥ b -[𝕜] a +ᵥ c] :=
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_segment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]
/-
**vadd_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vadd_openSegment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
 a +ᵥ openSegment 𝕜 b c = openSegment 𝕜 (a +ᵥ b) (a +ᵥ c)
参数：a : G；b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_openSegment`：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' o
penSegment 𝕜 a b = openSegment 𝕜 (f a) (f b)
· 使用定理 `VAddCommClass.vadd_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : VAdd M α} {inst_1 : VAdd N α} [self : VAddCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem vadd_openSegment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ openSegment 𝕜 b c = openSegment 𝕜 (a +ᵥ b) (a +ᵥ c) :=
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12286/
  we didn't need this `let` statement. -/
  let : AddTorsor E E := AddGroup.instAddTorsor E
  image_openSegment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c

@[simp]
/-
**mem_segment_translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_segment_translate (a : E) {x b c} : a + x in [a + b -[𝕜] a + c] ↔ x in
 [b -[𝕜] c]
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instVAddCommClassOfVAddAssocClass`：∀ {R : Type u_9} {M : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : VAdd R M] [VAddAssocClass R M M],   VAddCommClass
 R M M
· 使用定理 `VAddAssocClass.left`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M
] [inst_1 : AddAction M α], VAddAssocClass M M α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] := by
  simp_rw [← vadd_eq_add, ← vadd_segment, vadd_mem_vadd_set_iff]

@[simp]
/-
**mem_openSegment_translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_translate (a : E) {x b c : E} : a + x in openSegment 𝕜 (a 
+ b) (a + c) ↔ x in openSegment 𝕜 b c
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instVAddCommClassOfVAddAssocClass`：∀ {R : Type u_9} {M : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : VAdd R M] [VAddAssocClass R M M],   VAddCommClass
 R M M
· 使用定理 `VAddAssocClass.left`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M
] [inst_1 : AddAction M α], VAddAssocClass M M α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_openSegment_translate (a : E) {x b c : E} :
    a + x ∈ openSegment 𝕜 (a + b) (a + c) ↔ x ∈ openSegment 𝕜 b c := by
  simp_rw [← vadd_eq_add, ← vadd_openSegment, vadd_mem_vadd_set_iff]
/-
**segment_translate_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_translate_preimage (a b c : E) : (fun x => a + x) ⁻¹' [a + b -[𝕜] 
a + c] = [b -[𝕜] c]
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_segment_translate`：mem_segment_translate (a : E) {x b c} : a + x in 
[a + b -[𝕜] a + c] ↔ x in [b -[𝕜] c]
-/
theorem segment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
  Set.ext fun _ => mem_segment_translate 𝕜 a
/-
**openSegment_translate_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_translate_preimage (a b c : E) : (fun x => a + x) ⁻¹' openSegm
ent 𝕜 (a + b) (a + c) = openSegment 𝕜 b c
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_openSegment_translate`：mem_openSegment_translate (a : E) {x b c : E}
 : a + x in openSegment 𝕜 (a + b) (a + c) ↔ x in openSegment 𝕜 b c
-/
theorem openSegment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' openSegment 𝕜 (a + b) (a + c) = openSegment 𝕜 b c :=
  Set.ext fun _ => mem_openSegment_translate 𝕜 a
/-
**segment_translate_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a 
+ b -[𝕜] a + c]
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `segment_translate_preimage`：segment_translate_preimage (a b c : E) : (fu
n x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c]
· 使用定理 `add_left_surjective`：∀ {G : Type u_3} [inst : AddGroup G] (a : G), Funct
ion.Surjective fun x => a + x
-/
theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
  segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a
/-
**openSegment_translate_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_translate_image (a b c : E) : (fun x => a + x) '' openSegment 
𝕜 b c = openSegment 𝕜 (a + b) (a + c)
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `openSegment_translate_preimage`：openSegment_translate_preimage (a b c : 
E) : (fun x => a + x) ⁻¹' openSegment 𝕜 (a + b) (a + c) = openSegment 𝕜 b c
· 使用定理 `add_left_surjective`：∀ {G : Type u_3} [inst : AddGroup G] (a : G), Funct
ion.Surjective fun x => a + x
-/
theorem openSegment_translate_image (a b c : E) :
    (fun x => a + x) '' openSegment 𝕜 b c = openSegment 𝕜 (a + b) (a + c) :=
  openSegment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a
/-
**segment_inter_subset_endpoint_of_linearIndependent_sub** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：segment_inter_subset_endpoint_of_linearIndependent_sub {c x y : E} (h : Li
nearIndependent 𝕜 ![x - c, y - c]) : [c -[𝕜] x] inter [c -[𝕜] y] subseteq {c}
参数：h : LinearIndependent 𝕜 ![x - c, y - c]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
· 使用定理 `_private.Mathlib.Analysis.Convex.Segment.0.segment_inter_subset_endpoint
_of_linearIndependent_sub._abel_1_3`：∀ {E : Type u_1} [inst : AddCommGroup E] {c
 x : E}, x = x - c + c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_add_add_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a - c + (b + c) = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `LinearIndependent.eq_zero_of_pair'`：LinearIndependent.eq_zero_of_pair' {
x y : M} (h : LinearIndependent R ![x, y]) {s t : R} (h' : s • x = t • y) : s = 
0 ∧ t = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma segment_inter_subset_endpoint_of_linearIndependent_sub
    {c x y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) :
    [c -[𝕜] x] ∩ [c -[𝕜] y] ⊆ {c} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have Hx : x = (x - c) + c := by abel
  have Hy : y = (y - c) + c := by abel
  rw [Hx, Hy, smul_add, smul_add] at H
  have : c + q • (y - c) = c + p • (x - c) := by
    convert! H using 1 <;> simp [sub_smul]
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := h.eq_zero_of_pair' ((add_right_inj c).1 this).symm
  simp
/-
**segment_inter_eq_endpoint_of_linearIndependent_sub** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：segment_inter_eq_endpoint_of_linearIndependent_sub [ZeroLEOneClass 𝕜] {c x
 y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) : [c -[𝕜] x] inter [c -[𝕜] y] 
= {c}
参数：h : LinearIndependent 𝕜 ![x - c, y - c]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `segment_inter_subset_endpoint_of_linearIndependent_sub`：segment_inter_su
bset_endpoint_of_linearIndependent_sub {c x y : E} (h : LinearIndependent 𝕜 ![x 
- c, y - c]) : [c -[𝕜] x] inter [c -[𝕜] y] s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma segment_inter_eq_endpoint_of_linearIndependent_sub [ZeroLEOneClass 𝕜]
    {c x y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) :
    [c -[𝕜] x] ∩ [c -[𝕜] y] = {c} := by
  refine (segment_inter_subset_endpoint_of_linearIndependent_sub 𝕜 h).antisymm ?_
  simp [singleton_subset_iff, left_mem_segment]

end OrderedRing

/-
**sameRay_of_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_of_mem_segment [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 
𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E} (h : x in [y -[𝕜] z]) : SameRay 𝕜 (
x - y) (z - x)
参数：h : x in [y -[𝕜] z]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image'`：segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜
 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `SameRay.nonneg_smul_right`：nonneg_smul_right (h : SameRay R x y) (ha : 0
 <= a) : SameRay R x (a • y)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `SameRay.sameRay_nonneg_smul_left`：sameRay_nonneg_smul_left (v : M) (ha :
 0 <= a) : SameRay R (a • v) v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
-/
theorem sameRay_of_mem_segment [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {x y z : E}
    (h : x ∈ [y -[𝕜] z]) : SameRay 𝕜 (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel_left, ← sub_sub, sub_smul, one_smul] using
    (SameRay.sameRay_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)
/-
**segment_inter_eq_endpoint_of_linearIndependent_of_ne** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：segment_inter_eq_endpoint_of_linearIndependent_of_ne [CommRing 𝕜] [Partial
Order 𝕜] [IsOrderedRing 𝕜] [IsDomain 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y : E} 
(h : LinearIndependent 𝕜 ![x, y]) {s t : 𝕜} (hs : s != t) (c : E) : [c + x -[𝕜] 
c + t • y] inter [c + x -[𝕜] c + s • y] = {c + x}
参数：h : LinearIndependent 𝕜 ![x, y]；hs : s != t；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `segment_inter_eq_endpoint_of_linearIndependent_sub`：segment_inter_eq_end
point_of_linearIndependent_sub [ZeroLEOneClass 𝕜] {c x y : E} (h : LinearIndepen
dent 𝕜 ![x - c, y - c]) : [c -[𝕜] x] int…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIndependent.pair_add_smul_add_smul_iff`：∀ {R : Type u_2} {M : Type
 u_4} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x 
y : M}   {S : Type u_6} [inst_3 : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 44 条，此处仅展示前 30 条）
-/
lemma segment_inter_eq_endpoint_of_linearIndependent_of_ne
    [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [IsDomain 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {x y : E} (h : LinearIndependent 𝕜 ![x, y]) {s t : 𝕜} (hs : s ≠ t) (c : E) :
    [c + x -[𝕜] c + t • y] ∩ [c + x -[𝕜] c + s • y] = {c + x} := by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  simp only [add_sub_add_left_eq_sub]
  suffices H : LinearIndependent 𝕜 ![(-1 : 𝕜) • x + t • y, (-1 : 𝕜) • x + s • y] by
    convert! H using 1; simp only [neg_smul, one_smul]; abel_nf
  nontriviality 𝕜
  rw [LinearIndependent.pair_add_smul_add_smul_iff]
  aesop

section LinearOrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y : E}

/-
**midpoint_mem_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_mem_openSegment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y i
n openSegment 𝕜 x y
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image_lineMap`：openSegment_eq_image_lineMap (x y : E) : o
penSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `invOf_pos`：invOf_pos [Invertible a] : 0 < ⅟a ↔ 0 < a
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `invOf_lt_one`：invOf_lt_one [Invertible a] (h : 1 < a) : ⅟a < 1
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem midpoint_mem_openSegment [Invertible (2 : 𝕜)] (x y : E) :
    midpoint 𝕜 x y ∈ openSegment 𝕜 x y := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨⅟2, ⟨invOf_pos.mpr two_pos, invOf_lt_one one_lt_two⟩, rfl⟩
/-
**midpoint_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y in [x
 -[𝕜] y]
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `midpoint_mem_openSegment`：midpoint_mem_openSegment [Invertible (2 : 𝕜)] 
(x y : E) : midpoint 𝕜 x y in openSegment 𝕜 x y
-/
theorem midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y ∈ [x -[𝕜] y] :=
  openSegment_subset_segment _ _ _ <| midpoint_mem_openSegment _ _
/-
**mem_openSegment_sub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x in openSegment 
𝕜 (x - y) (x + y)
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_sub_add`：midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y
) = x
· 使用定理 `midpoint_mem_openSegment`：midpoint_mem_openSegment [Invertible (2 : 𝕜)] 
(x y : E) : midpoint 𝕜 x y in openSegment 𝕜 x y
-/
theorem mem_openSegment_sub_add [Invertible (2 : 𝕜)] (x y : E) :
    x ∈ openSegment 𝕜 (x - y) (x + y) := by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x - y) (x + y)
  rw [midpoint_sub_add]
/-
**mem_segment_sub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x in [x - y -[𝕜] x + 
y]
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `mem_openSegment_sub_add`：mem_openSegment_sub_add [Invertible (2 : 𝕜)] (x
 y : E) : x in openSegment 𝕜 (x - y) (x + y)
-/
theorem mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x - y -[𝕜] x + y] :=
  openSegment_subset_segment _ _ _ <| mem_openSegment_sub_add _ _
/-
**mem_openSegment_add_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x in openSegment 
𝕜 (x + y) (x - y)
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_add_sub`：midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y
) = x
· 使用定理 `midpoint_mem_openSegment`：midpoint_mem_openSegment [Invertible (2 : 𝕜)] 
(x y : E) : midpoint 𝕜 x y in openSegment 𝕜 x y
-/
theorem mem_openSegment_add_sub [Invertible (2 : 𝕜)] (x y : E) :
    x ∈ openSegment 𝕜 (x + y) (x - y) := by
  convert! midpoint_mem_openSegment (𝕜 := 𝕜) (x + y) (x - y)
  rw [midpoint_add_sub]
/-
**mem_segment_add_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x in [x + y -[𝕜] x - 
y]
参数：2 : 𝕜；x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `mem_openSegment_add_sub`：mem_openSegment_add_sub [Invertible (2 : 𝕜)] (x
 y : E) : x in openSegment 𝕜 (x + y) (x - y)
-/
theorem mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x + y -[𝕜] x - y] :=
  openSegment_subset_segment _ _ _ <| mem_openSegment_add_sub _ _

@[simp]
/-
**left_mem_openSegment_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] : x in ope
nSegment 𝕜 x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `openSegment_same`：openSegment_same (x : E) : openSegment 𝕜 x x = {x}
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem left_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] :
    x ∈ openSegment 𝕜 x y ↔ x = y := by
  constructor
  · rintro ⟨a, b, _, hb, hab, hx⟩
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 ?_)
    rw [hx, ← add_smul, hab, one_smul]
  · rintro rfl
    rw [openSegment_same]
    exact mem_singleton _

@[simp]
/-
**right_mem_openSegment_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] : y in op
enSegment 𝕜 x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_symm`：openSegment_symm (x y : E) : openSegment 𝕜 x y = openS
egment 𝕜 y x
· 使用定理 `left_mem_openSegment_iff`：left_mem_openSegment_iff [DenselyOrdered 𝕜] [I
sTorsionFree 𝕜 E] : x in openSegment 𝕜 x y ↔ x = y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem right_mem_openSegment_iff [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] :
    y ∈ openSegment 𝕜 x y ↔ x = y := by rw [openSegment_symm, left_mem_openSegment_iff, eq_comm]

end LinearOrderedRing

section LinearOrderedSemifield

variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {x y z : E}

/-
**mem_segment_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_segment_iff_div : x in [y -[𝕜] z] ↔ exists a b : 𝕜, 0 <= a ∧ 0 <= b ∧ 
0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem mem_segment_iff_div :
    x ∈ [y -[𝕜] z] ↔
      ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div, div_self hab.ne']
/-
**mem_openSegment_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_iff_div : x in openSegment 𝕜 y z ↔ exists a b : 𝕜, 0 < a ∧
 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem mem_openSegment_iff_div : x ∈ openSegment 𝕜 y z ↔
    ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab, div_one, div_one]
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := add_pos' ha hb
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div, div_self hab.ne']

end LinearOrderedSemifield

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}

/-
**mem_segment_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_segment_iff_sameRay : x in [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sameRay_of_mem_segment`：sameRay_of_mem_segment [CommRing 𝕜] [PartialOrde
r 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E} (h : x in
 [y -[𝕜] z])…
· 使用定理 `SameRay.exists_eq_smul_add`：exists_eq_smul_add (h : SameRay R v₁ v₂) : e
xists a b : R, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ +
 v₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_segment_translate`：mem_segment_translate (a : E) {x b c} : a + x in 
[a + b -[𝕜] a + c] ↔ x in [b -[𝕜] c]
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem mem_segment_iff_sameRay : x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x) := by
  refine ⟨sameRay_of_mem_segment, fun h => ?_⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_comm, sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x), neg_add_cancel]
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, ?_⟩
  rw [← sub_eq_neg_add, ← neg_sub, hxy, ← sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_cancel]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/-- If `z = lineMap x y c` is a point on the line passing through `x` and `y`, then the open
segment `openSegment 𝕜 x y` is included in the union of the open segments `openSegment 𝕜 x z`,
`openSegment 𝕜 z y`, and the point `z`. Informally, `(x, y) ⊆ {z} ∪ (x, z) ∪ (z, y)`. -/
/-
**openSegment_subset_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_union (x y : E) {z : E} (hz : z in range (lineMap x y :
 𝕜 -> E)) : openSegment 𝕜 x y subseteq insert z (openSegment 𝕜 x z union openSeg
ment 𝕜 z y)
参数：x y : E；hz : z in range (lineMap x y : 𝕜 -> E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image_lineMap`：openSegment_eq_image_lineMap (x y : E) : o
penSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `z = lineMap x y c` is a point on the line passing through `x` and `y`, then 
the open
segment `openSegment 𝕜 x y` is included in the union of the open segments `openS
egment 𝕜 x z`,
`openSegment 𝕜 z y`, and the point `z`. Informally, `(x, y) ⊆ {z} ∪ (x, z) ∪ (z,
 y)`.
-/
theorem openSegment_subset_union (x y : E) {z : E} (hz : z ∈ range (lineMap x y : 𝕜 → E)) :
    openSegment 𝕜 x y ⊆ insert z (openSegment 𝕜 x z ∪ openSegment 𝕜 z y) := by
  rcases hz with ⟨c, rfl⟩
  simp only [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  rintro a ⟨h₀, h₁⟩
  rcases lt_trichotomy a c with (hac | rfl | hca)
  · right
    left
    have hc : 0 < c := h₀.trans hac
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, div_mul_cancel₀ _ hc.ne']
  · left
    rfl
  · right
    right
    have hc : 0 < 1 - c := sub_pos.2 (hca.trans h₁)
    simp only [← lineMap_apply_one_sub y]
    refine
      ⟨(a - c) / (1 - c), ⟨div_pos (sub_pos.2 hca) hc, (div_lt_one hc).2 <| sub_lt_sub_right h₁ _⟩,
        ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, sub_mul, one_mul,
      div_mul_cancel₀ _ hc.ne', sub_sub_sub_cancel_right]

end LinearOrderedField

/-!
#### Segments in an ordered space

Relates `segment`, `openSegment` and `Set.Icc`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`
-/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section OrderedAddCommMonoid

variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {x y : E}

/-
**segment_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subseteq Icc x y
参数：h : x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem segment_subset_Icc (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ ≤ a • x + b • y := by gcongr
  · calc
      a • x + b • y ≤ a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid E] [PartialOrder E] [IsOrderedCancelAddMonoid E]
  [Module 𝕜 E] [PosSMulStrictMono 𝕜 E] {x y : E}

/-
**openSegment_subset_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_Ioo (h : x < y) : openSegment 𝕜 x y subseteq Ioo x y
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem openSegment_subset_Ioo (h : x < y) : openSegment 𝕜 x y ⊆ Ioo x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ < a • x + b • y := by gcongr
  · calc
      a • x + b • y < a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {a b : 𝕜}

/-
**segment_subset_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_uIcc (x y : E) : [x -[𝕜] y] subseteq uIcc x y
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `segment_subset_Icc`：segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subsete
q Icc x y
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
-/
theorem segment_subset_uIcc (x y : E) : [x -[𝕜] y] ⊆ uIcc x y := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]
    exact segment_subset_Icc h
  · rw [uIcc_of_ge h, segment_symm]
    exact segment_subset_Icc h
/-
**Convex.min_le_combo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.min_le_combo (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1
) : min x y <= a • x + b • y
参数：x y : E；ha : 0 <= a；hb : 0 <= b；hab : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `segment_subset_uIcc`：segment_subset_uIcc (x y : E) : [x -[𝕜] y] subseteq
 uIcc x y
-/
theorem Convex.min_le_combo (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    min x y ≤ a • x + b • y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1
/-
**Convex.combo_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_le_max (x y : E) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1
) : a • x + b • y <= max x y
参数：x y : E；ha : 0 <= a；hb : 0 <= b；hab : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `segment_subset_uIcc`：segment_subset_uIcc (x y : E) : [x -[𝕜] y] subseteq
 uIcc x y
-/
theorem Convex.combo_le_max (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ≤ max x y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

/-
**Icc_subset_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_subset_segment : Icc x y subseteq [x -[𝕜] y]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_same`：segment_same (x : E) : [x -[𝕜] x] = {x}
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
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
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
（共 34 条，此处仅展示前 30 条）
-/
theorem Icc_subset_segment : Icc x y ⊆ [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div,
      div_eq_iff h.ne', add_comm, sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]

@[simp]
/-
**segment_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `segment_subset_Icc`：segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subsete
q Icc x y
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
· 使用定理 `Icc_subset_segment`：Icc_subset_segment : Icc x y subseteq [x -[𝕜] y]
-/
theorem segment_eq_Icc (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment
/-
**Ioo_subset_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_subset_openSegment : Ioo x y subseteq openSegment 𝕜 x y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_openSegment_of_ne_left_right`：mem_openSegment_of_ne_left_right (hx :
 x != z) (hy : y != z) (hz : z in [x -[𝕜] y]) : z in openSegment 𝕜 x y
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Icc_subset_segment`：Icc_subset_segment : Icc x y subseteq [x -[𝕜] y]
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
theorem Ioo_subset_openSegment : Ioo x y ⊆ openSegment 𝕜 x y := fun _ hz =>
  mem_openSegment_of_ne_left_right hz.1.ne hz.2.ne' <| Icc_subset_segment <| Ioo_subset_Icc_self hz

@[simp]
/-
**openSegment_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y = Ioo x y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `openSegment_subset_Ioo`：openSegment_subset_Ioo (h : x < y) : openSegment
 𝕜 x y subseteq Ioo x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Ioo_subset_openSegment`：Ioo_subset_openSegment : Ioo x y subseteq openSe
gment 𝕜 x y
-/
theorem openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y = Ioo x y :=
  (openSegment_subset_Ioo h).antisymm Ioo_subset_openSegment
/-
**segment_eq_Icc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y)
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]
/-
**openSegment_eq_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_eq_Ioo' (hxy : x != y) : openSegment 𝕜 x y = Ioo (min x y) (ma
x x y)
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_Ioo`：openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y =
 Ioo x y
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `openSegment_symm`：openSegment_symm (x y : E) : openSegment 𝕜 x y = openS
egment 𝕜 y x
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem openSegment_eq_Ioo' (hxy : x ≠ y) : openSegment 𝕜 x y = Ioo (min x y) (max x y) := by
  rcases hxy.lt_or_gt with h | h
  · rw [openSegment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le]
  · rw [openSegment_symm, openSegment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le]
/-
**segment_eq_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `segment_eq_Icc'`：segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) 
(max x y)
-/
theorem segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y :=
  segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
/-
**Convex.mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_Icc (h : x <= y) : z in Icc x y ↔ exists a b, 0 <= a ∧ 0 <= b ∧
 a + b = 1 ∧ a * x + b * y = z
参数：h : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point is in an `Icc` iff it can be expressed as a convex combination of the en
dpoints.
-/
theorem Convex.mem_Icc (h : x ≤ y) :
    z ∈ Icc x y ↔ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  simp only [← segment_eq_Icc h, segment, mem_ofPred_eq, smul_eq_mul, exists_and_left]

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
/-
**Convex.mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_Ioo (h : x < y) : z in Ioo x y ↔ exists a b, 0 < a ∧ 0 < b ∧ a 
+ b = 1 ∧ a * x + b * y = z
参数：h : x < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `openSegment_eq_Ioo`：openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y =
 Ioo x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point is in an `Ioo` iff it can be expressed as a strict convex combination of
 the endpoints.
-/
theorem Convex.mem_Ioo (h : x < y) :
    z ∈ Ioo x y ↔ ∃ a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  simp only [← openSegment_eq_Ioo h, openSegment, smul_eq_mul, exists_and_left, mem_ofPred_eq]

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
/-
**Convex.mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_Ioc (h : x < y) : z in Ioc x y ↔ exists a b, 0 <= a ∧ 0 < b ∧ a
 + b = 1 ∧ a * x + b * y = z
参数：h : x < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Convex.mem_Icc`：Convex.mem_Icc (h : x <= y) : z in Icc x y ↔ exists a b,
 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a * x + b * y = z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Convex.mem_Ioo`：Convex.mem_Ioo (h : x < y) : z in Ioo x y ↔ exists a b, 
0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z

--- 原说明 ---
A point is in an `Ioc` iff it can be expressed as a semistrict convex combinatio
n of the
endpoints.
-/
theorem Convex.mem_Ioc (h : x < y) :
    z ∈ Ioc x y ↔ ∃ a b, 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rw [hab, one_mul, zero_mul, add_zero] at hz
      exact (hz.1.ne rfl).elim
    · exact ⟨a, b, ha, hb', hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rwa [hab, one_mul, zero_mul, zero_add, right_mem_Ioc]
    · exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩)

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
/-
**Convex.mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_Ico (h : x < y) : z in Ico x y ↔ exists a b, 0 < a ∧ 0 <= b ∧ a
 + b = 1 ∧ a * x + b * y = z
参数：h : x < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Convex.mem_Icc`：Convex.mem_Icc (h : x <= y) : z in Icc x y ↔ exists a b,
 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ a * x + b * y = z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Convex.mem_Ioo`：Convex.mem_Ioo (h : x < y) : z in Ioo x y ↔ exists a b, 
0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z

--- 原说明 ---
A point is in an `Ico` iff it can be expressed as a semistrict convex combinatio
n of the
endpoints.
-/
theorem Convex.mem_Ico (h : x < y) :
    z ∈ Ico x y ↔ ∃ a b, 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rw [hab, one_mul, zero_mul, zero_add] at hz
      exact (hz.2.ne rfl).elim
    · exact ⟨a, b, ha', hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rwa [hab, one_mul, zero_mul, add_zero, left_mem_Ico]
    · exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩)

end LinearOrderedField

namespace Nonneg

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

/-
**Nonneg.Icc_subset_segment** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStr
ictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   Set.Icc x y ⊆ segment { t // 0 ≤ t }
 x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Icc_subset_segment`：Icc_subset_segment : Icc x y subseteq [x -[𝕜] y]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
protected lemma Icc_subset_segment {x y : {t : 𝕜 // 0 ≤ t}} :
    Icc x y ⊆ segment {t : 𝕜 // 0 ≤ t} x y := by
  intro a ⟨hxa, hay⟩
  rw [← Subtype.coe_le_coe] at hxa hay
  rcases Icc_subset_segment ⟨hxa, hay⟩ with ⟨t₁, t₂, t₁_nonneg, t₂_nonneg, t_add, hta⟩
  refine ⟨⟨t₁, t₁_nonneg⟩, ⟨t₂, t₂_nonneg⟩, zero_le, zero_le, ?_, ?_⟩ <;>
  ext <;> simpa
/-
**Nonneg.segment_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStr
ictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   x ≤ y → segment { t // 0 ≤ t } x y =
 Set.Icc x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `segment_subset_Icc`：segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subsete
q Icc x y
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Nonneg.Icc_subset_segment`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : L
inearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   Set.Icc
 x y ⊆ segment …
-/
protected lemma segment_eq_Icc {x y : {t : 𝕜 // 0 ≤ t}} (hxy : x ≤ y) :
    segment {t : 𝕜 // 0 ≤ t} x y = Icc x y := by
  refine subset_antisymm (segment_subset_Icc hxy) Nonneg.Icc_subset_segment
/-
**Nonneg.segment_eq_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : IsStr
ictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   segment { t // 0 ≤ t } x y = Set.uIc
c x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nonneg.segment_eq_Icc`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : Linea
rOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] {x y : { t // 0 ≤ t }},   x ≤ y → seg
ment { t //…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
-/
protected lemma segment_eq_uIcc {x y : {t : 𝕜 // 0 ≤ t}} :
    segment {t : 𝕜 // 0 ≤ t} x y = uIcc x y := by
  rcases le_total x y with h | h
  · simp [h, Nonneg.segment_eq_Icc]
  · simp [h, segment_symm _ x y, Nonneg.segment_eq_Icc]

end Nonneg

namespace Prod

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/-
**Prod.segment_subset** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：segment_subset (x y : E × F) : segment 𝕜 x y subseteq segment 𝕜 x.1 y.1 ×ˢ
 segment 𝕜 x.2 y.2
参数：x y : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem segment_subset (x y : E × F) : segment 𝕜 x y ⊆ segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩
/-
**Prod.openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：openSegment_subset (x y : E × F) : openSegment 𝕜 x y subseteq openSegment 
𝕜 x.1 y.1 ×ˢ openSegment 𝕜 x.2 y.2
参数：x y : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem openSegment_subset (x y : E × F) :
    openSegment 𝕜 x y ⊆ openSegment 𝕜 x.1 y.1 ×ˢ openSegment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩
/-
**Prod.image_mk_segment_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：image_mk_segment_left (x₁ x₂ : E) (y : F) : (fun x => (x, y)) '' [x₁ -[𝕜] 
x₂] = [(x₁, y) -[𝕜] (x₂, y)]
参数：x₁ x₂ : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image₂`：segment_eq_image₂ (x y : E) : [x -[𝕜] y] = (fun p : 𝕜
 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 <= p.1 ∧ 0 <= p.2 ∧ p.1 + p.2 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mk_segment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' [x₁ -[𝕜] x₂] = [(x₁, y) -[𝕜] (x₂, y)] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
/-
**Prod.image_mk_segment_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：image_mk_segment_right (x : E) (y₁ y₂ : F) : (fun y => (x, y)) '' [y₁ -[𝕜]
 y₂] = [(x, y₁) -[𝕜] (x, y₂)]
参数：x : E；y₁ y₂ : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image₂`：segment_eq_image₂ (x y : E) : [x -[𝕜] y] = (fun p : 𝕜
 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 <= p.1 ∧ 0 <= p.2 ∧ p.1 + p.2 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mk_segment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' [y₁ -[𝕜] y₂] = [(x, y₁) -[𝕜] (x, y₂)] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
/-
**Prod.image_mk_openSegment_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：image_mk_openSegment_left (x₁ x₂ : E) (y : F) : (fun x => (x, y)) '' openS
egment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y)
参数：x₁ x₂ : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image₂`：openSegment_eq_image₂ (x y : E) : openSegment 𝕜 x
 y = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2
 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mk_openSegment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]

@[simp]
/-
**Prod.image_mk_openSegment_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：image_mk_openSegment_right (x : E) (y₁ y₂ : F) : (fun y => (x, y)) '' open
Segment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y₂)
参数：x : E；y₁ y₂ : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image₂`：openSegment_eq_image₂ (x y : E) : openSegment 𝕜 x
 y = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2
 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mk_openSegment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' openSegment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y₂) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]

end Prod

namespace Pi

variable [Semiring 𝕜] [PartialOrder 𝕜] [∀ i, AddCommMonoid (M i)] [∀ i, Module 𝕜 (M i)] {s : Set ι}

/-
**Pi.segment_subset** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：segment_subset (x y : forall i, M i) : segment 𝕜 x y subseteq s.pi fun i =
> segment 𝕜 (x i) (y i)
参数：x y : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem segment_subset (x y : ∀ i, M i) : segment 𝕜 x y ⊆ s.pi fun i => segment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩
/-
**Pi.openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：openSegment_subset (x y : forall i, M i) : openSegment 𝕜 x y subseteq s.pi
 fun i => openSegment 𝕜 (x i) (y i)
参数：x y : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem openSegment_subset (x y : ∀ i, M i) :
    openSegment 𝕜 x y ⊆ s.pi fun i => openSegment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩

variable [DecidableEq ι]
/-
**Pi.image_update_segment** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：image_update_segment (i : ι) (x₁ x₂ : M i) (y : forall i, M i) : update y 
i '' [x₁ -[𝕜] x₂] = [update y i x₁ -[𝕜] update y i x₂]
参数：i : ι；x₁ x₂ : M i；y : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image₂`：segment_eq_image₂ (x y : E) : [x -[𝕜] y] = (fun p : 𝕜
 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 <= p.1 ∧ 0 <= p.2 ∧ p.1 + p.2 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_update_segment (i : ι) (x₁ x₂ : M i) (y : ∀ i, M i) :
    update y i '' [x₁ -[𝕜] x₂] = [update y i x₁ -[𝕜] update y i x₂] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]
/-
**Pi.image_update_openSegment** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：image_update_openSegment (i : ι) (x₁ x₂ : M i) (y : forall i, M i) : updat
e y i '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (update y i x₁) (update y i x₂)
参数：i : ι；x₁ x₂ : M i；y : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image₂`：openSegment_eq_image₂ (x y : E) : openSegment 𝕜 x
 y = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2
 = 1 }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_update_openSegment (i : ι) (x₁ x₂ : M i) (y : ∀ i, M i) :
    update y i '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (update y i x₁) (update y i x₂) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]

end Pi

