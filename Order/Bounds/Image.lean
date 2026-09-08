/-
Copyright (c) 2017 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Paul Lezeau
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Order.Bounds.Basic

/-!

# Images of upper/lower bounds under monotone functions

In this file we prove various results about the behaviour of bounds under monotone/antitone maps.
-/

public section

open Function Set

open OrderDual (toDual ofDual)

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace MonotoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

@[to_dual]
/-
**MonotoneOn.mem_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：mem_upperBounds_image (Hf : MonotoneOn f t) (Hst : s subseteq t) (Has : a 
in upperBounds s) (Hat : a in t) : f a in upperBounds (f '' s)
参数：Hf : MonotoneOn f t；Hst : s subseteq t；Has : a in upperBounds s；Hat : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem mem_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) (Has : a ∈ upperBounds s)
    (Hat : a ∈ t) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

@[to_dual]
/-
**MonotoneOn.mem_upperBounds_image_self** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：mem_upperBounds_image_self (Hf : MonotoneOn f t) : a in upperBounds t -> a
 in t -> f a in upperBounds (f '' t)
参数：Hf : MonotoneOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mem_upperBounds_image`：mem_upperBounds_image (Hf : MonotoneOn
 f t) (Hst : s subseteq t) (Has : a in upperBounds s) (Hat : a in t) : f a in up
perBounds (f '' s)
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem mem_upperBounds_image_self (Hf : MonotoneOn f t) :
    a ∈ upperBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.mem_upperBounds_image subset_rfl

@[to_dual]
/-
**MonotoneOn.image_upperBounds_subset_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空
间 `MonotoneOn`。
形式化陈述：image_upperBounds_subset_upperBounds_image (Hf : MonotoneOn f t) (Hst : s 
subseteq t) : f '' (upperBounds s inter t) subseteq upperBounds (f '' s)
参数：Hf : MonotoneOn f t；Hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mem_upperBounds_image`：mem_upperBounds_image (Hf : MonotoneOn
 f t) (Hst : s subseteq t) (Has : a in upperBounds s) (Hat : a in t) : f a in up
perBounds (f '' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem image_upperBounds_subset_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
@[to_dual /-- The image under a monotone function on a set `t` of a subset which has a lower bound
in `t` is bounded below. -/]
/-
**MonotoneOn.map_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：map_bddAbove (Hf : MonotoneOn f t) (Hst : s subseteq t) : (upperBounds s i
nter t).Nonempty -> BddAbove (f '' s)
参数：Hf : MonotoneOn f t；Hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mem_upperBounds_image`：mem_upperBounds_image (Hf : MonotoneOn
 f t) (Hst : s subseteq t) (Has : a in upperBounds s) (Hat : a in t) : f a in up
perBounds (f '' s)
-/
theorem map_bddAbove (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
@[to_dual /-- A monotone map sends a greatest element of a set to a greatest element of its
image. -/]
/-
**MonotoneOn.map_isLeast** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast t a) : IsLeast (f '' t) (f
 a)
参数：Hf : MonotoneOn f t；Ha : IsLeast t a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MonotoneOn.mem_lowerBounds_image_self`：∀ {α : Type u} {β : Type v} [inst
 : Preorder α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   Monotone
On f t → a ∈ lowerBounds t …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

@[to_dual]
/-
**AntitoneOn.mem_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：mem_upperBounds_image (Hf : AntitoneOn f t) (Hst : s subseteq t) (Has : a 
in lowerBounds s) : a in t -> f a in upperBounds (f '' s)
参数：Hf : AntitoneOn f t；Hst : s subseteq t；Has : a in lowerBounds s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mem_lowerBounds_image`：∀ {α : Type u} {β : Type v} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β} {s t : Set α} {a : α},   MonotoneOn 
f t → s ⊆ t → a ∈ lowe…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem mem_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) (Has : a ∈ lowerBounds s) :
    a ∈ t → f a ∈ upperBounds (f '' s) :=
  Hf.dual_right.mem_lowerBounds_image Hst Has

@[to_dual]
/-
**AntitoneOn.mem_upperBounds_image_self** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：mem_upperBounds_image_self (Hf : AntitoneOn f t) : a in lowerBounds t -> a
 in t -> f a in upperBounds (f '' t)
参数：Hf : AntitoneOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mem_lowerBounds_image_self`：∀ {α : Type u} {β : Type v} [inst
 : Preorder α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   Monotone
On f t → a ∈ lowerBounds t …
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem mem_upperBounds_image_self (Hf : AntitoneOn f t) :
    a ∈ lowerBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.dual_right.mem_lowerBounds_image_self

@[to_dual]
/-
**AntitoneOn.image_lowerBounds_subset_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空
间 `AntitoneOn`。
形式化陈述：image_lowerBounds_subset_upperBounds_image (Hf : AntitoneOn f t) (Hst : s 
subseteq t) : f '' (lowerBounds s inter t) subseteq upperBounds (f '' s)
参数：Hf : AntitoneOn f t；Hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.image_lowerBounds_subset_lowerBounds_image`：∀ {α : Type u} {β
 : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s t : Set α}, 
  MonotoneOn f t → s ⊆ t → f '' (lowerBound…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem image_lowerBounds_subset_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    f '' (lowerBounds s ∩ t) ⊆ upperBounds (f '' s) :=
  Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
@[to_dual /-- The image under an antitone function of a set which is bounded below is bounded
above. -/]
/-
**AntitoneOn.map_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：map_bddAbove (Hf : AntitoneOn f t) (Hst : s subseteq t) : (upperBounds s i
nter t).Nonempty -> BddBelow (f '' s)
参数：Hf : AntitoneOn f t；Hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_bddAbove`：map_bddAbove (Hf : MonotoneOn f t) (Hst : s sub
seteq t) : (upperBounds s inter t).Nonempty -> BddAbove (f '' s)
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem map_bddAbove (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bddAbove Hst

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
@[to_dual /-- An antitone map sends a least element of a set to a greatest element of its
image. -/]
/-
**AntitoneOn.map_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：map_isGreatest (Hf : AntitoneOn f t) : IsGreatest t a -> IsLeast (f '' t) 
(f a)
参数：Hf : AntitoneOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   MonotoneOn f t → IsG
reatest t a → I…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem map_isGreatest (Hf : AntitoneOn f t) : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_isGreatest

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf

@[to_dual]
/-
**Monotone.mem_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：mem_upperBounds_image (Ha : a in upperBounds s) : f a in upperBounds (f ''
 s)
参数：Ha : a in upperBounds s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem mem_upperBounds_image (Ha : a ∈ upperBounds s) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

@[to_dual]
/-
**Monotone.image_upperBounds_subset_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 
`Monotone`。
形式化陈述：image_upperBounds_subset_upperBounds_image : f '' upperBounds s subseteq u
pperBounds (f '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
-/
theorem image_upperBounds_subset_upperBounds_image :
    f '' upperBounds s ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`BddAbove.image2`. -/
@[to_dual /-- The image under a monotone function of a set which is bounded below is bounded below.
See also `BddBelow.image2`. -/]
/-
**Monotone.map_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → BddAbove (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
-/
theorem map_bddAbove : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upperBounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
@[to_dual /-- A monotone map sends a greatest element of a set to a greatest element of its
image. -/]
/-
**Monotone.map_isLeast** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a)
参数：Ha : IsLeast s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Monotone.mem_lowerBounds_image`：∀ {α : Type u} {β : Type v} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α},
 a ∈ lowerBounds s →…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

include hf

@[to_dual]
/-
**Antitone.mem_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：mem_upperBounds_image : a in lowerBounds s -> f a in upperBounds (f '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.mem_lowerBounds_image`：∀ {α : Type u} {β : Type v} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α},
 a ∈ lowerBounds s →…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem mem_upperBounds_image : a ∈ lowerBounds s → f a ∈ upperBounds (f '' s) :=
  hf.dual_right.mem_lowerBounds_image

@[to_dual]
/-
**Antitone.image_lowerBounds_subset_upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 
`Antitone`。
形式化陈述：image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s subseteq u
pperBounds (f '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.image_lowerBounds_subset_lowerBounds_image`：∀ {α : Type u} {β :
 Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀
 {s : Set α}, f '' lowerBounds s ⊆ lowerB…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s ⊆ upperBounds (f '' s) :=
  hf.dual_right.image_lowerBounds_subset_lowerBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
@[to_dual /-- The image under an antitone function of a set which is bounded below is bounded
above. -/]
/-
**Antitone.map_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：map_bddAbove : BddAbove s -> BddBelow (f '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem map_bddAbove : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bddAbove

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
@[to_dual /-- An antitone map sends a least element of a set to a greatest element of its
image. -/]
/-
**Antitone.map_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：map_isGreatest : IsGreatest s a -> IsLeast (f '' s) (f a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α}, IsGrea
test s a → Is…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem map_isGreatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_isGreatest

end Antitone

section StrictMono

variable [LinearOrder α] [Preorder β] {f : α → β} {a : α} {s : Set α}

/-
**StrictMono.mem_upperBounds_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mem_upperBounds_image (hf : StrictMono f) : f a in upperBounds 
(f '' s) ↔ a in upperBounds s
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictMono.mem_upperBounds_image (hf : StrictMono f) :
    f a ∈ upperBounds (f '' s) ↔ a ∈ upperBounds s := by simp [upperBounds, hf.le_iff_le]
/-
**StrictMono.mem_lowerBounds_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mem_lowerBounds_image (hf : StrictMono f) : f a in lowerBounds 
(f '' s) ↔ a in lowerBounds s
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictMono.mem_lowerBounds_image (hf : StrictMono f) :
    f a ∈ lowerBounds (f '' s) ↔ a ∈ lowerBounds s := by simp [lowerBounds, hf.le_iff_le]
/-
**StrictMono.map_isLeast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.map_isLeast (hf : StrictMono f) : IsLeast (f '' s) (f a) ↔ IsLe
ast s a
参数：hf : StrictMono f。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `StrictMono.mem_lowerBounds_image`：StrictMono.mem_lowerBounds_image (hf :
 StrictMono f) : f a in lowerBounds (f '' s) ↔ a in lowerBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictMono.map_isLeast (hf : StrictMono f) : IsLeast (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, hf.injective.eq_iff, hf.mem_lowerBounds_image]
/-
**StrictMono.map_isGreatest** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.map_isGreatest (hf : StrictMono f) : IsGreatest (f '' s) (f a) 
↔ IsGreatest s a
参数：hf : StrictMono f。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `StrictMono.mem_upperBounds_image`：StrictMono.mem_upperBounds_image (hf :
 StrictMono f) : f a in upperBounds (f '' s) ↔ a in upperBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictMono.map_isGreatest (hf : StrictMono f) :
    IsGreatest (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictMono

section StrictAnti

variable [LinearOrder α] [Preorder β] {f : α → β} {a : α} {s : Set α}

/-
**StrictAnti.mem_upperBounds_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mem_upperBounds_image (hf : StrictAnti f) : f a in upperBounds 
(f '' s) ↔ a in lowerBounds s
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictAnti.mem_upperBounds_image (hf : StrictAnti f) :
    f a ∈ upperBounds (f '' s) ↔ a ∈ lowerBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]
/-
**StrictAnti.mem_lowerBounds_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mem_lowerBounds_image (hf : StrictAnti f) : f a in lowerBounds 
(f '' s) ↔ a in upperBounds s
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictAnti.mem_lowerBounds_image (hf : StrictAnti f) :
    f a ∈ lowerBounds (f '' s) ↔ a ∈ upperBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]
/-
**StrictAnti.map_isLeast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.map_isLeast (hf : StrictAnti f) : IsLeast (f '' s) (f a) ↔ IsGr
eatest s a
参数：hf : StrictAnti f。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用引理 `StrictAnti.mem_lowerBounds_image`：StrictAnti.mem_lowerBounds_image (hf :
 StrictAnti f) : f a in lowerBounds (f '' s) ↔ a in upperBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictAnti.map_isLeast (hf : StrictAnti f) : IsLeast (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_lowerBounds_image]
/-
**StrictAnti.map_isGreatest** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.map_isGreatest (hf : StrictAnti f) : IsGreatest (f '' s) (f a) 
↔ IsLeast s a
参数：hf : StrictAnti f。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用引理 `StrictAnti.mem_upperBounds_image`：StrictAnti.mem_upperBounds_image (hf :
 StrictAnti f) : f a in upperBounds (f '' s) ↔ a in lowerBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma StrictAnti.map_isGreatest (hf : StrictAnti f) : IsGreatest (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictAnti

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

@[to_dual]
/-
**mem_upperBounds_image2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperBounds_image2 (ha : a in upperBounds s) (hb : b in upperBounds t)
 : f a b in upperBounds (image2 f s t)
参数：ha : a in upperBounds s；hb : b in upperBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mem_upperBounds_image2 (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

@[to_dual]
/-
**image2_upperBounds_upperBounds_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image2_upperBounds_upperBounds_subset : image2 f (upperBounds s) (upperBou
nds t) subseteq upperBounds (image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `mem_upperBounds_image2`：mem_upperBounds_image2 (ha : a in upperBounds s)
 (hb : b in upperBounds t) : f a b in upperBounds (image2 f s t)
-/
theorem image2_upperBounds_upperBounds_subset :
    image2 f (upperBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_upperBounds_image2 h₀ h₁ ha hb

/-- See also `Monotone.map_bddAbove`. -/
@[to_dual /-- See also `Monotone.map_bddBelow`. -/]
/-
**BddAbove.image2** 是 Mathlib 中的一个定理，位于命名空间 `BddAbove`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {f : α → β → γ}   {s : Set α} {t : Set β},   (∀ (
b : β), Monotone (Function.swap f b)) →     (∀ (a : α), Monotone (f a)) → BddAbo
ve s → BddAbove t → BddAbove (Set.image2 f s t)
参数：∀ (b : β), Monotone (Function.swap f b)；∀ (a : α), Monotone (f a)；Set.image2 
f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_upperBounds_image2`：mem_upperBounds_image2 (ha : a in upperBounds s)
 (hb : b in upperBounds t) : f a b in upperBounds (image2 f s t)

--- 原说明 ---
See also `Monotone.map_bddAbove`.
-/
protected theorem BddAbove.image2 :
    BddAbove s → BddAbove t → BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

@[to_dual]
/-
**IsGreatest.image2** 是 Mathlib 中的一个定理，位于命名空间 `IsGreatest`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {f : α → β → γ}   {s : Set α} {t : Set β} {a : α}
 {b : β},   (∀ (b : β), Monotone (Function.swap f b)) →     (∀ (a : α), Monotone
 (f a)) → IsGreatest s a → IsGreatest t b → IsGreatest (Set.image2 f s t) (f a b
)
参数：∀ (b : β), Monotone (Function.swap f b)；∀ (a : α), Monotone (f a)；Set.image2 
f s t；f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_upperBounds_image2`：mem_upperBounds_image2 (ha : a in upperBounds s)
 (hb : b in upperBounds t) : f a b in upperBounds (image2 f s t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

@[to_dual]
/-
**mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a in up
perBounds s) (hb : b in lowerBounds t) : f a b in upperBounds (image2 f s t)
参数：ha : a in upperBounds s；hb : b in lowerBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

@[to_dual]
/-
**image2_upperBounds_lowerBounds_subset_upperBounds_image2** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：image2_upperBounds_lowerBounds_subset_upperBounds_image2 : image2 f (upper
Bounds s) (lowerBounds t) subseteq upperBounds (image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a in upperBounds s) (hb
 : b in lowerBounds t) : f a b in upperBounds (ima…
-/
theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]
/-
**BddAbove.bddAbove_image2_of_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.bddAbove_image2_of_bddBelow : BddAbove s -> BddBelow t -> BddAbov
e (Set.image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a in upperBounds s) (hb
 : b in lowerBounds t) : f a b in upperBounds (ima…
-/
theorem BddAbove.bddAbove_image2_of_bddBelow :
    BddAbove s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]
/-
**IsGreatest.isGreatest_image2_of_isLeast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeas
t t b) : IsGreatest (Set.image2 f s t) (f a b)
参数：ha : IsGreatest s a；hb : IsLeast t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a in upperBounds s) (hb
 : b in lowerBounds t) : f a b in upperBounds (ima…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

@[to_dual]
/-
**mem_upperBounds_image2_of_mem_lowerBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperBounds_image2_of_mem_lowerBounds (ha : a in lowerBounds s) (hb : 
b in lowerBounds t) : f a b in upperBounds (image2 f s t)
参数：ha : a in lowerBounds s；hb : b in lowerBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mem_upperBounds_image2_of_mem_lowerBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

@[to_dual]
/-
**image2_upperBounds_upperBounds_subset_upperBounds_image2** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：image2_upperBounds_upperBounds_subset_upperBounds_image2 : image2 f (lower
Bounds s) (lowerBounds t) subseteq upperBounds (image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `mem_upperBounds_image2_of_mem_lowerBounds`：mem_upperBounds_image2_of_mem
_lowerBounds (ha : a in lowerBounds s) (hb : b in lowerBounds t) : f a b in uppe
rBounds (image2 f s t)
-/
theorem image2_upperBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]
/-
**BddBelow.image2_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.image2_bddAbove : BddBelow s -> BddBelow t -> BddAbove (Set.image
2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_upperBounds_image2_of_mem_lowerBounds`：mem_upperBounds_image2_of_mem
_lowerBounds (ha : a in lowerBounds s) (hb : b in lowerBounds t) : f a b in uppe
rBounds (image2 f s t)
-/
theorem BddBelow.image2_bddAbove : BddBelow s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]
/-
**IsLeast.isGreatest_image2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) : IsGreate
st (Set.image2 f s t) (f a b)
参数：ha : IsLeast s a；hb : IsLeast t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_upperBounds_image2_of_mem_lowerBounds`：mem_upperBounds_image2_of_mem
_lowerBounds (ha : a in lowerBounds s) (hb : b in lowerBounds t) : f a b in uppe
rBounds (image2 f s t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

@[to_dual]
/-
**mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a in lo
werBounds s) (hb : b in upperBounds t) : f a b in upperBounds (image2 f s t)
参数：ha : a in lowerBounds s；hb : b in upperBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

@[to_dual]
/-
**image2_lowerBounds_upperBounds_subset_upperBounds_image2** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：image2_lowerBounds_upperBounds_subset_upperBounds_image2 : image2 f (lower
Bounds s) (upperBounds t) subseteq upperBounds (image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a in lowerBounds s) (hb
 : b in upperBounds t) : f a b in upperBounds (ima…
-/
theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

@[to_dual]
/-
**BddBelow.bddAbove_image2_of_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.bddAbove_image2_of_bddAbove : BddBelow s -> BddAbove t -> BddAbov
e (Set.image2 f s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a in lowerBounds s) (hb
 : b in upperBounds t) : f a b in upperBounds (ima…
-/
theorem BddBelow.bddAbove_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

@[to_dual]
/-
**IsLeast.isGreatest_image2_of_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreates
t t b) : IsGreatest (Set.image2 f s t) (f a b)
参数：ha : IsLeast s a；hb : IsGreatest t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds`：mem_upperB
ounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a in lowerBounds s) (hb
 : b in upperBounds t) : f a b in upperBounds (ima…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneMonotone

end Image2

section IsCofinalFor
variable {α β : Type*} [Preorder α] [Preorder β] {s t : Set α} {f : α → β}

@[to_dual]
/-
**IsCofinalFor.image_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCofinalFor.image_of_monotone (hst : IsCofinalFor s t) (hf : Monotone f) 
: IsCofinalFor (f '' s) (f '' t)
参数：hst : IsCofinalFor s t；hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsCofinalFor.image_of_monotone (hst : IsCofinalFor s t) (hf : Monotone f) :
    IsCofinalFor (f '' s) (f '' t) := by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

@[to_dual]
/-
**IsCofinalFor.image_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCofinalFor.image_of_antitone (hst : IsCofinalFor s t) (hf : Antitone f) 
: IsCoinitialFor (f '' s) (f '' t)
参数：hst : IsCofinalFor s t；hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsCofinalFor.image_of_antitone (hst : IsCofinalFor s t) (hf : Antitone f) :
    IsCoinitialFor (f '' s) (f '' t) := by
  simp only [IsCoinitialFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

end IsCofinalFor

section Prod

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_dual]
/-
**bddAbove_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_prod {s : Set (α × β)} : BddAbove s ↔ BddAbove (Prod.fst '' s) ∧ 
BddAbove (Prod.snd '' s)
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma bddAbove_prod {s : Set (α × β)} :
    BddAbove s ↔ BddAbove (Prod.fst '' s) ∧ BddAbove (Prod.snd '' s) :=
  ⟨fun ⟨p, hp⟩ ↦ ⟨⟨p.1, forall_mem_image.2 fun _q hq ↦ (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq ↦ (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨⟨x, y⟩, fun _p hp ↦
      ⟨hx <| mem_image_of_mem _ hp, hy <| mem_image_of_mem _ hp⟩⟩⟩

@[to_dual]
/-
**bddAbove_range_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_range_prod {F : ι -> α × β} : BddAbove (range F) ↔ BddAbove (rang
e <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F)
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
lemma bddAbove_range_prod {F : ι → α × β} :
    BddAbove (range F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F) := by
  simp only [bddAbove_prod, ← range_comp]

@[to_dual]
/-
**isLUB_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_prod {s : Set (α × β)} {p : α × β} : IsLUB s p ↔ IsLUB (Prod.fst '' 
s) p.1 ∧ IsLUB (Prod.snd '' s) p.2
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
-/
theorem isLUB_prod {s : Set (α × β)} {p : α × β} :
    IsLUB s p ↔ IsLUB (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2 := by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) ∈ upperBounds s from (H.2 h).1
    exact fun q hq => ⟨ha <| mem_image_of_mem _ hq, (H.1 hq).2⟩
  · suffices h : (p.1, a) ∈ upperBounds s from (H.2 h).2
    exact fun q hq => ⟨(H.1 hq).1, ha <| mem_image_of_mem _ hq⟩
  · exact fun q hq => ⟨H.1.1 <| mem_image_of_mem _ hq, H.2.1 <| mem_image_of_mem _ hq⟩
  · exact fun q hq =>
      ⟨H.1.2 <| monotone_fst.mem_upperBounds_image hq,
        H.2.2 <| monotone_snd.mem_upperBounds_image hq⟩
/-
**Monotone.upperBounds_image_of_directedOn_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g 
: α × β -> γ} (hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· <= ·) d) :
 upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d))
参数：hg : Monotone g；α × β；hd : DirectedOn (· <= ·) d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `upperBounds_mono_of_isCofinalFor`：upperBounds_mono_of_isCofinalFor (hst 
: IsCofinalFor s t) : upperBounds t subseteq upperBounds s
· 使用引理 `IsCofinalFor.image_of_monotone`：IsCofinalFor.image_of_monotone (hst : Is
CofinalFor s t) (hf : Monotone f) : IsCofinalFor (f '' s) (f '' t)
· 使用引理 `DirectedOn.isCofinalFor_fst_image_prod_snd_image`：DirectedOn.isCofinalFo
r_fst_image_prod_snd_image {β : Type*} [Preorder β] {s : Set (α × β)} (hs : Dire
ctedOn (· <= ·) s) : IsCofinalFor ((Pr…
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.subset_fst_image_prod_snd_image`：subset_fst_image_prod_snd_image {s 
: Set (α × β)} : s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s)
-/
lemma Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β → γ}
    (hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := le_antisymm
  (upperBounds_mono_of_isCofinalFor (hd.isCofinalFor_fst_image_prod_snd_image.image_of_monotone hg))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))

end Prod


section Pi

variable {π : α → Type*} [∀ a, Preorder (π a)]

@[to_dual]
/-
**bddAbove_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_pi {s : Set (forall a, π a)} : BddAbove s ↔ forall a, BddAbove (F
unction.eval a '' s)
参数：forall a, π a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma bddAbove_pi {s : Set (∀ a, π a)} :
    BddAbove s ↔ ∀ a, BddAbove (Function.eval a '' s) :=
  ⟨fun ⟨f, hf⟩ a ↦ ⟨f a, forall_mem_image.2 fun _ hg ↦ hf hg a⟩,
    fun h ↦ ⟨fun a ↦ (h a).some, fun _ hg a ↦ (h a).some_mem <| mem_image_of_mem _ hg⟩⟩

@[to_dual]
/-
**bddAbove_range_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_range_pi {F : ι -> forall a, π a} : BddAbove (range F) ↔ forall a
, BddAbove (range fun i => F i a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bddAbove_range_pi {F : ι → ∀ a, π a} :
    BddAbove (range F) ↔ ∀ a, BddAbove (range fun i ↦ F i a) := by
  simp only [bddAbove_pi, ← range_comp]
  rfl

@[to_dual]
/-
**isLUB_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_pi {s : Set (forall a, π a)} {f : forall a, π a} : IsLUB s f ↔ foral
l a, IsLUB (Function.eval a '' s) (f a)
参数：forall a, π a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
· 使用定理 `Function.monotone_eval`：Function.monotone_eval {ι : Type u} {α : ι -> Ty
pe v} [forall i, Preorder (α i)] (i : ι) : Monotone (Function.eval i : (forall i
, α i) -> α …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_update_iff`：le_update_iff : x <= Function.update y i a ↔ x i <= a ∧ f
orall (j) (_ : j != i), x j <= y j
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem isLUB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsLUB s f ↔ ∀ a, IsLUB (Function.eval a '' s) (f a) := by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b ∈ upperBounds s from Function.update_self a b f ▸ H.2 h a
      exact fun g hg => le_update_iff.2 ⟨hb <| mem_image_of_mem _ hg, fun i _ => H.1 hg i⟩
    · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upperBounds_image hg)

end Pi

@[to_dual]
/-
**IsGLB.of_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (hf : forall {x y}, 
f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x
参数：hf : forall {x y}, f x <= f y ↔ x <= y；hx : IsGLB (f '' s) (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Monotone.mem_lowerBounds_image`：∀ {α : Type u} {β : Type v} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α},
 a ∈ lowerBounds s →…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsGLB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

@[to_dual (reorder := f g)]
/-
**BddAbove.range_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.range_mono [Preorder β] {f : α -> β} (g : α -> β) (h : forall a, 
f a <= g a) (hbdd : BddAbove (range g)) : BddAbove (range f)
参数：g : α -> β；h : forall a, f a <= g a；hbdd : BddAbove (range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma BddAbove.range_mono [Preorder β] {f : α → β} (g : α → β) (h : ∀ a, f a ≤ g a)
    (hbdd : BddAbove (range g)) : BddAbove (range f) := by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

@[to_dual]
/-
**BddAbove.range_comp_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.range_comp_left {γ : Type*} [Preorder β] [Preorder γ] {f : α -> β
} {g : β -> γ} (hf : BddAbove (range f)) (hg : Monotone g) : BddAbove (range (fu
n x => g (f x)))
参数：hf : BddAbove (range f)；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
-/
lemma BddAbove.range_comp_left {γ : Type*} [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : BddAbove (range f)) (hg : Monotone g) : BddAbove (range (fun x => g (f x))) := by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

@[deprecated BddAbove.range_comp_left (since := "2026-06-07")]
alias BddAbove.range_comp := BddAbove.range_comp_left

@[deprecated BddBelow.range_comp_left (since := "2026-06-07")]
alias BddBelow.range_comp := BddBelow.range_comp_left
