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

variable [Preorder α] [Preorder β] {f : α -> β} {s t : Set α} {a : α}

@[to_dual]
/--
theorem `mem_upperBounds_image` / 定理 `mem_upperBounds_image`

English:
theorem mem_upperBounds_image
  statement: (Hf : MonotoneOn f t) (Hst : s subseteq t) (Has : a in upperBounds s)
  proof: forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

@[to_dual]

中文:
定理 mem_upperBounds_image
  结论: (Hf : MonotoneOn f t) (Hst : s subseteq t) (Has : a in upperBounds s)
  证明: forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

@[to_dual]

Depends on / 依赖: forall_mem_image
-/
theorem mem_upperBounds_image (Hf : MonotoneOn f t) (Hst : s subseteq t) (Has : a in upperBounds s)
    (Hat : a in t) : f a in upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

@[to_dual]
/--
theorem `mem_upperBounds_image_self` / 定理 `mem_upperBounds_image_self`

English:
theorem mem_upperBounds_image_self
  given: (Hf : MonotoneOn f t)
  proof: Hf.mem_upperBounds_image subset_rfl

@[to_dual]

中文:
定理 mem_upperBounds_image_self
  条件: (Hf : MonotoneOn f t)
  证明: Hf.mem_upperBounds_image subset_rfl

@[to_dual]

Depends on / 依赖: Hf.mem_upperBounds_image, mem_upperBounds_image, subset_rfl
-/
theorem mem_upperBounds_image_self (Hf : MonotoneOn f t) :
    a in upperBounds t -> a in t -> f a in upperBounds (f '' t) :=
  Hf.mem_upperBounds_image subset_rfl

@[to_dual]
/--
theorem `image_upperBounds_subset_upperBounds_image` / 定理 `image_upperBounds_subset_upperBounds_image`

English:
theorem image_upperBounds_subset_upperBounds_image
  given: (Hf : MonotoneOn f t) (Hst : s subseteq t)
  proof: by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

中文:
定理 image_upperBounds_subset_upperBounds_image
  条件: (Hf : MonotoneOn f t) (Hst : s subseteq t)
  证明: by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

Depends on / 依赖: Hf.mem_upperBounds_image, mem_upperBounds_image
-/
theorem image_upperBounds_subset_upperBounds_image (Hf : MonotoneOn f t) (Hst : s subseteq t) :
    f '' (upperBounds s inter t) subseteq upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
@[to_dual /-- The image under a monotone function on a set `t` of a subset which has a lower bound
in `t` is bounded below. -/]
/--
theorem `map_bddAbove` / 定理 `map_bddAbove`

English:
theorem map_bddAbove
  given: (Hf : MonotoneOn f t) (Hst : s subseteq t)
  proof: fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩

中文:
定理 map_bddAbove
  条件: (Hf : MonotoneOn f t) (Hst : s subseteq t)
  证明: fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩
-/
theorem map_bddAbove (Hf : MonotoneOn f t) (Hst : s subseteq t) :
    (upperBounds s inter t).Nonempty -> BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
@[to_dual /-- A monotone map sends a greatest element of a set to a greatest element of its
image. -/]
/--
theorem `map_isLeast` / 定理 `map_isLeast`

English:
theorem map_isLeast
  given: (Hf : MonotoneOn f t) (Ha : IsLeast t a)
  statement: IsLeast (f '' t) (f a)
  proof: ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

中文:
定理 map_isLeast
  条件: (Hf : MonotoneOn f t) (Ha : IsLeast t a)
  结论: IsLeast (f '' t) (f a)
  证明: ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

Depends on / 依赖: Hf.mem_lowerBounds_image_self, mem_image_of_mem, mem_lowerBounds_image_self
-/
theorem map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α -> β} {s t : Set α} {a : α}

@[to_dual]
/--
theorem `mem_upperBounds_image` / 定理 `mem_upperBounds_image`

English:
theorem mem_upperBounds_image
  given: (Hf : AntitoneOn f t) (Hst : s subseteq t) (Has : a in lowerBounds s)
  proof: Hf.dual_right.mem_lowerBounds_image Hst Has

@[to_dual]

中文:
定理 mem_upperBounds_image
  条件: (Hf : AntitoneOn f t) (Hst : s subseteq t) (Has : a in lowerBounds s)
  证明: Hf.dual_right.mem_lowerBounds_image Hst Has

@[to_dual]

Depends on / 依赖: Hf.dual_right.mem_lowerBounds_image, dual_right, mem_lowerBounds_image
-/
theorem mem_upperBounds_image (Hf : AntitoneOn f t) (Hst : s subseteq t) (Has : a in lowerBounds s) :
    a in t -> f a in upperBounds (f '' s) :=
  Hf.dual_right.mem_lowerBounds_image Hst Has

@[to_dual]
/--
theorem `mem_upperBounds_image_self` / 定理 `mem_upperBounds_image_self`

English:
theorem mem_upperBounds_image_self
  given: (Hf : AntitoneOn f t)
  proof: Hf.dual_right.mem_lowerBounds_image_self

@[to_dual]

中文:
定理 mem_upperBounds_image_self
  条件: (Hf : AntitoneOn f t)
  证明: Hf.dual_right.mem_lowerBounds_image_self

@[to_dual]

Depends on / 依赖: Hf.dual_right.mem_lowerBounds_image_self, dual_right, mem_lowerBounds_image_self
-/
theorem mem_upperBounds_image_self (Hf : AntitoneOn f t) :
    a in lowerBounds t -> a in t -> f a in upperBounds (f '' t) :=
  Hf.dual_right.mem_lowerBounds_image_self

@[to_dual]
/--
theorem `image_lowerBounds_subset_upperBounds_image` / 定理 `image_lowerBounds_subset_upperBounds_image`

English:
theorem image_lowerBounds_subset_upperBounds_image
  given: (Hf : AntitoneOn f t) (Hst : s subseteq t)
  proof: Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

中文:
定理 image_lowerBounds_subset_upperBounds_image
  条件: (Hf : AntitoneOn f t) (Hst : s subseteq t)
  证明: Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

Depends on / 依赖: Hf.dual_right.image_lowerBounds_subset_lowerBounds_image, dual_right, image_lowerBounds_subset_lowerBounds_image
-/
theorem image_lowerBounds_subset_upperBounds_image (Hf : AntitoneOn f t) (Hst : s subseteq t) :
    f '' (lowerBounds s inter t) subseteq upperBounds (f '' s) :=
  Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
@[to_dual /-- The image under an antitone function of a set which is bounded below is bounded
above. -/]
/--
theorem `map_bddAbove` / 定理 `map_bddAbove`

English:
theorem map_bddAbove
  given: (Hf : AntitoneOn f t) (Hst : s subseteq t)
  proof: Hf.dual_right.map_bddAbove Hst

中文:
定理 map_bddAbove
  条件: (Hf : AntitoneOn f t) (Hst : s subseteq t)
  证明: Hf.dual_right.map_bddAbove Hst

Depends on / 依赖: Hf.dual_right.map_bddAbove, dual_right, map_bddAbove
-/
theorem map_bddAbove (Hf : AntitoneOn f t) (Hst : s subseteq t) :
    (upperBounds s inter t).Nonempty -> BddBelow (f '' s) :=
  Hf.dual_right.map_bddAbove Hst

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
@[to_dual /-- An antitone map sends a least element of a set to a greatest element of its
image. -/]
/--
theorem `map_isGreatest` / 定理 `map_isGreatest`

English:
theorem map_isGreatest
  given: (Hf : AntitoneOn f t)
  statement: IsGreatest t a -> IsLeast (f '' t) (f a)
  proof: Hf.dual_right.map_isGreatest

中文:
定理 map_isGreatest
  条件: (Hf : AntitoneOn f t)
  结论: IsGreatest t a -> IsLeast (f '' t) (f a)
  证明: Hf.dual_right.map_isGreatest

Depends on / 依赖: Hf.dual_right.map_isGreatest, dual_right, map_isGreatest
-/
theorem map_isGreatest (Hf : AntitoneOn f t) : IsGreatest t a -> IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_isGreatest

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α -> β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf

@[to_dual]
/--
theorem `mem_upperBounds_image` / 定理 `mem_upperBounds_image`

English:
theorem mem_upperBounds_image
  given: (Ha : a in upperBounds s)
  statement: f a in upperBounds (f '' s)
  proof: forall_mem_image.2 fun _ H => Hf (Ha H)

@[to_dual]

中文:
定理 mem_upperBounds_image
  条件: (Ha : a in upperBounds s)
  结论: f a in upperBounds (f '' s)
  证明: forall_mem_image.2 fun _ H => Hf (Ha H)

@[to_dual]

Depends on / 依赖: forall_mem_image
-/
theorem mem_upperBounds_image (Ha : a in upperBounds s) : f a in upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

@[to_dual]
/--
theorem `image_upperBounds_subset_upperBounds_image` / 定理 `image_upperBounds_subset_upperBounds_image`

English:
theorem image_upperBounds_subset_upperBounds_image
  proof: by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

中文:
定理 image_upperBounds_subset_upperBounds_image
  证明: by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

Depends on / 依赖: Hf.mem_upperBounds_image, mem_upperBounds_image
-/
theorem image_upperBounds_subset_upperBounds_image :
    f '' upperBounds s subseteq upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`BddAbove.image2`. -/
@[to_dual /-- The image under a monotone function of a set which is bounded below is bounded below.
See also `BddBelow.image2`. -/]
/--
theorem `map_bddAbove` / 定理 `map_bddAbove`

English:
theorem map_bddAbove
  statement: BddAbove s -> BddAbove (f '' s)

中文:
定理 map_bddAbove
  结论: BddAbove s -> BddAbove (f '' s)
-/
theorem map_bddAbove : BddAbove s -> BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upperBounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
@[to_dual /-- A monotone map sends a greatest element of a set to a greatest element of its
image. -/]
/--
theorem `map_isLeast` / 定理 `map_isLeast`

English:
theorem map_isLeast
  given: (Ha : IsLeast s a)
  statement: IsLeast (f '' s) (f a)
  proof: ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

中文:
定理 map_isLeast
  条件: (Ha : IsLeast s a)
  结论: IsLeast (f '' s) (f a)
  证明: ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

Depends on / 依赖: Hf.mem_lowerBounds_image, mem_image_of_mem, mem_lowerBounds_image
-/
theorem map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α -> β} (hf : Antitone f) {a : α} {s : Set α}

include hf

@[to_dual]
/--
theorem `mem_upperBounds_image` / 定理 `mem_upperBounds_image`

English:
theorem mem_upperBounds_image
  statement: a in lowerBounds s -> f a in upperBounds (f '' s)
  proof: hf.dual_right.mem_lowerBounds_image

@[to_dual]

中文:
定理 mem_upperBounds_image
  结论: a in lowerBounds s -> f a in upperBounds (f '' s)
  证明: hf.dual_right.mem_lowerBounds_image

@[to_dual]

Depends on / 依赖: dual_right, hf.dual_right.mem_lowerBounds_image, mem_lowerBounds_image
-/
theorem mem_upperBounds_image : a in lowerBounds s -> f a in upperBounds (f '' s) :=
  hf.dual_right.mem_lowerBounds_image

@[to_dual]
/--
theorem `image_lowerBounds_subset_upperBounds_image` / 定理 `image_lowerBounds_subset_upperBounds_image`

English:
theorem image_lowerBounds_subset_upperBounds_image
  statement: f '' lowerBounds s subseteq upperBounds (f '' s)
  proof: hf.dual_right.image_lowerBounds_subset_lowerBounds_image

中文:
定理 image_lowerBounds_subset_upperBounds_image
  结论: f '' lowerBounds s subseteq upperBounds (f '' s)
  证明: hf.dual_right.image_lowerBounds_subset_lowerBounds_image

Depends on / 依赖: dual_right, hf.dual_right.image_lowerBounds_subset_lowerBounds_image, image_lowerBounds_subset_lowerBounds_image
-/
theorem image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s subseteq upperBounds (f '' s) :=
  hf.dual_right.image_lowerBounds_subset_lowerBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
@[to_dual /-- The image under an antitone function of a set which is bounded below is bounded
above. -/]
/--
theorem `map_bddAbove` / 定理 `map_bddAbove`

English:
theorem map_bddAbove
  statement: BddAbove s -> BddBelow (f '' s)
  proof: hf.dual_right.map_bddAbove

中文:
定理 map_bddAbove
  结论: BddAbove s -> BddBelow (f '' s)
  证明: hf.dual_right.map_bddAbove

Depends on / 依赖: dual_right, hf.dual_right.map_bddAbove, map_bddAbove
-/
theorem map_bddAbove : BddAbove s -> BddBelow (f '' s) :=
  hf.dual_right.map_bddAbove

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
@[to_dual /-- An antitone map sends a least element of a set to a greatest element of its
image. -/]
/--
theorem `map_isGreatest` / 定理 `map_isGreatest`

English:
theorem map_isGreatest
  statement: IsGreatest s a -> IsLeast (f '' s) (f a)
  proof: hf.dual_right.map_isGreatest

中文:
定理 map_isGreatest
  结论: IsGreatest s a -> IsLeast (f '' s) (f a)
  证明: hf.dual_right.map_isGreatest

Depends on / 依赖: dual_right, hf.dual_right.map_isGreatest, map_isGreatest
-/
theorem map_isGreatest : IsGreatest s a -> IsLeast (f '' s) (f a) :=
  hf.dual_right.map_isGreatest

end Antitone

section StrictMono

variable [LinearOrder α] [Preorder β] {f : α -> β} {a : α} {s : Set α}

/--
lemma `StrictMono.mem_upperBounds_image` / 引理 `StrictMono.mem_upperBounds_image`

English:
lemma StrictMono.mem_upperBounds_image
  given: (hf : StrictMono f)
  proof: by simp [upperBounds, hf.le_iff_le]

中文:
引理 严格递增.mem_upperBounds_image
  条件: (hf : 严格递增 f)
  证明: by simp [upperBounds, hf.le_iff_le]

Depends on / 依赖: hf.le_iff_le, le_iff_le, upperBounds
-/
lemma StrictMono.mem_upperBounds_image (hf : StrictMono f) :
    f a in upperBounds (f '' s) ↔ a in upperBounds s := by simp [upperBounds, hf.le_iff_le]

/--
lemma `StrictMono.mem_lowerBounds_image` / 引理 `StrictMono.mem_lowerBounds_image`

English:
lemma StrictMono.mem_lowerBounds_image
  given: (hf : StrictMono f)
  proof: by simp [lowerBounds, hf.le_iff_le]

中文:
引理 严格递增.mem_lowerBounds_image
  条件: (hf : 严格递增 f)
  证明: by simp [lowerBounds, hf.le_iff_le]

Depends on / 依赖: hf.le_iff_le, le_iff_le, lowerBounds
-/
lemma StrictMono.mem_lowerBounds_image (hf : StrictMono f) :
    f a in lowerBounds (f '' s) ↔ a in lowerBounds s := by simp [lowerBounds, hf.le_iff_le]

/--
lemma `StrictMono.map_isLeast` / 引理 `StrictMono.map_isLeast`

English:
lemma StrictMono.map_isLeast
  given: (hf : StrictMono f)
  statement: IsLeast (f '' s) (f a) ↔ IsLeast s a
  proof: by
  simp [IsLeast, hf.injective.eq_iff, hf.mem_lowerBounds_image]

中文:
引理 严格递增.map_isLeast
  条件: (hf : 严格递增 f)
  结论: IsLeast (f '' s) (f a) ↔ IsLeast s a
  证明: by
  simp [IsLeast, hf.injective.eq_iff, hf.mem_lowerBounds_image]

Depends on / 依赖: IsLeast, eq_iff, hf.injective.eq_iff, hf.mem_lowerBounds_image, injective, mem_lowerBounds_image
-/
lemma StrictMono.map_isLeast (hf : StrictMono f) : IsLeast (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, hf.injective.eq_iff, hf.mem_lowerBounds_image]

/--
lemma `StrictMono.map_isGreatest` / 引理 `StrictMono.map_isGreatest`

English:
lemma StrictMono.map_isGreatest
  given: (hf : StrictMono f)
  proof: by
  simp [IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

中文:
引理 严格递增.map_isGreatest
  条件: (hf : 严格递增 f)
  证明: by
  simp [IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

Depends on / 依赖: IsGreatest, eq_iff, hf.injective.eq_iff, hf.mem_upperBounds_image, injective, mem_upperBounds_image
-/
lemma StrictMono.map_isGreatest (hf : StrictMono f) :
    IsGreatest (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictMono

section StrictAnti

variable [LinearOrder α] [Preorder β] {f : α -> β} {a : α} {s : Set α}

/--
lemma `StrictAnti.mem_upperBounds_image` / 引理 `StrictAnti.mem_upperBounds_image`

English:
lemma StrictAnti.mem_upperBounds_image
  given: (hf : StrictAnti f)
  proof: by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

中文:
引理 严格递减.mem_upperBounds_image
  条件: (hf : 严格递减 f)
  证明: by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

Depends on / 依赖: hf.le_iff_ge, le_iff_ge, lowerBounds, upperBounds
-/
lemma StrictAnti.mem_upperBounds_image (hf : StrictAnti f) :
    f a in upperBounds (f '' s) ↔ a in lowerBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

/--
lemma `StrictAnti.mem_lowerBounds_image` / 引理 `StrictAnti.mem_lowerBounds_image`

English:
lemma StrictAnti.mem_lowerBounds_image
  given: (hf : StrictAnti f)
  proof: by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

中文:
引理 严格递减.mem_lowerBounds_image
  条件: (hf : 严格递减 f)
  证明: by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

Depends on / 依赖: hf.le_iff_ge, le_iff_ge, lowerBounds, upperBounds
-/
lemma StrictAnti.mem_lowerBounds_image (hf : StrictAnti f) :
    f a in lowerBounds (f '' s) ↔ a in upperBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

/--
lemma `StrictAnti.map_isLeast` / 引理 `StrictAnti.map_isLeast`

English:
lemma StrictAnti.map_isLeast
  given: (hf : StrictAnti f)
  statement: IsLeast (f '' s) (f a) ↔ IsGreatest s a
  proof: by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_lowerBounds_image]

中文:
引理 严格递减.map_isLeast
  条件: (hf : 严格递减 f)
  结论: IsLeast (f '' s) (f a) ↔ IsGreatest s a
  证明: by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_lowerBounds_image]

Depends on / 依赖: IsGreatest, IsLeast, eq_iff, hf.injective.eq_iff, hf.mem_lowerBounds_image, injective, mem_lowerBounds_image
-/
lemma StrictAnti.map_isLeast (hf : StrictAnti f) : IsLeast (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_lowerBounds_image]

/--
lemma `StrictAnti.map_isGreatest` / 引理 `StrictAnti.map_isGreatest`

English:
lemma StrictAnti.map_isGreatest
  given: (hf : StrictAnti f)
  statement: IsGreatest (f '' s) (f a) ↔ IsLeast s a
  proof: by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

中文:
引理 严格递减.map_isGreatest
  条件: (hf : 严格递减 f)
  结论: IsGreatest (f '' s) (f a) ↔ IsLeast s a
  证明: by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

Depends on / 依赖: IsGreatest, IsLeast, eq_iff, hf.injective.eq_iff, hf.mem_upperBounds_image, injective, mem_upperBounds_image
-/
lemma StrictAnti.map_isGreatest (hf : StrictAnti f) : IsGreatest (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictAnti

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α -> β -> γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : forall b, Monotone (swap f b)) (h₁ : forall a, Monotone (f a))

include h₀ h₁

@[to_dual]
/--
theorem `mem_upperBounds_image2` / 定理 `mem_upperBounds_image2`

English:
theorem mem_upperBounds_image2
  given: (ha : a in upperBounds s) (hb : b in upperBounds t)
  proof: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

中文:
定理 mem_upperBounds_image2
  条件: (ha : a in upperBounds s) (hb : b in upperBounds t)
  证明: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

Depends on / 依赖: forall_mem_image2
-/
theorem mem_upperBounds_image2 (ha : a in upperBounds s) (hb : b in upperBounds t) :
    f a b in upperBounds (image2 f s t) :=
forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]
/--
theorem `image2_upperBounds_upperBounds_subset` / 定理 `image2_upperBounds_upperBounds_subset`

English:
theorem image2_upperBounds_upperBounds_subset
  proof: image2_subset_iff.2 fun _ ha _ hb => mem_upperBounds_image2 h₀ h₁ ha hb

中文:
定理 image2_upperBounds_upperBounds_subset
  证明: image2_subset_iff.2 fun _ ha _ hb => mem_upperBounds_image2 h₀ h₁ ha hb

Depends on / 依赖: image2_subset_iff, mem_upperBounds_image2
-/
theorem image2_upperBounds_upperBounds_subset :
    image2 f (upperBounds s) (upperBounds t) subseteq upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb => mem_upperBounds_image2 h₀ h₁ ha hb

/-- See also `Monotone.map_bddAbove`. -/
@[to_dual /-- See also `Monotone.map_bddBelow`. -/]
/--
theorem `BddAbove.image2` / 定理 `BddAbove.image2`

English:
theorem BddAbove.image2
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

@[to_dual]

中文:
定理 BddAbove.image2
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

@[to_dual]
-/
protected theorem BddAbove.image2 :
    BddAbove s -> BddAbove t -> BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

@[to_dual]
/--
theorem `IsGreatest.image2` / 定理 `IsGreatest.image2`

English:
theorem IsGreatest.image2
  given: (ha : IsGreatest s a) (hb : IsGreatest t b)
  proof: ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩

中文:
定理 IsGreatest.image2
  条件: (ha : IsGreatest s a) (hb : IsGreatest t b)
  证明: ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩
-/
protected theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : forall b, Monotone (swap f b)) (h₁ : forall a, Antitone (f a))

include h₀ h₁

@[to_dual]
/--
theorem `mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds` / 定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds`

English:
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds
  statement: (ha : a in upperBounds s)
  proof: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

中文:
定理 mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds
  结论: (ha : a in upperBounds s)
  证明: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

Depends on / 依赖: forall_mem_image2
-/
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a in upperBounds s)
    (hb : b in lowerBounds t) : f a b in upperBounds (image2 f s t) :=
forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]
/--
theorem `image2_upperBounds_lowerBounds_subset_upperBounds_image2` / 定理 `image2_upperBounds_lowerBounds_subset_upperBounds_image2`

English:
theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2
  proof: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]

中文:
定理 image2_upperBounds_lowerBounds_subset_upperBounds_image2
  证明: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]

Depends on / 依赖: image2_subset_iff, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds
-/
theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) subseteq upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]
/--
theorem `BddAbove.bddAbove_image2_of_bddBelow` / 定理 `BddAbove.bddAbove_image2_of_bddBelow`

English:
theorem BddAbove.bddAbove_image2_of_bddBelow
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]

中文:
定理 BddAbove.bddAbove_image2_of_bddBelow
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]

Depends on / 依赖: mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds
-/
theorem BddAbove.bddAbove_image2_of_bddBelow :
    BddAbove s -> BddBelow t -> BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]
/--
theorem `IsGreatest.isGreatest_image2_of_isLeast` / 定理 `IsGreatest.isGreatest_image2_of_isLeast`

English:
theorem IsGreatest.isGreatest_image2_of_isLeast
  given: (ha : IsGreatest s a) (hb : IsLeast t b)
  proof: ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

中文:
定理 IsGreatest.isGreatest_image2_of_isLeast
  条件: (ha : IsGreatest s a) (hb : IsLeast t b)
  证明: ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

Depends on / 依赖: mem_image2_of_mem, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds
-/
theorem IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : forall b, Antitone (swap f b)) (h₁ : forall a, Antitone (f a))

include h₀ h₁

@[to_dual]
/--
theorem `mem_upperBounds_image2_of_mem_lowerBounds` / 定理 `mem_upperBounds_image2_of_mem_lowerBounds`

English:
theorem mem_upperBounds_image2_of_mem_lowerBounds
  statement: (ha : a in lowerBounds s)
  proof: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

中文:
定理 mem_upperBounds_image2_of_mem_lowerBounds
  结论: (ha : a in lowerBounds s)
  证明: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

Depends on / 依赖: forall_mem_image2
-/
theorem mem_upperBounds_image2_of_mem_lowerBounds (ha : a in lowerBounds s)
    (hb : b in lowerBounds t) : f a b in upperBounds (image2 f s t) :=
forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]
/--
theorem `image2_upperBounds_upperBounds_subset_upperBounds_image2` / 定理 `image2_upperBounds_upperBounds_subset_upperBounds_image2`

English:
theorem image2_upperBounds_upperBounds_subset_upperBounds_image2
  proof: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]

中文:
定理 image2_upperBounds_upperBounds_subset_upperBounds_image2
  证明: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]

Depends on / 依赖: image2_subset_iff, mem_upperBounds_image2_of_mem_lowerBounds
-/
theorem image2_upperBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) subseteq upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

@[to_dual]
/--
theorem `BddBelow.image2_bddAbove` / 定理 `BddBelow.image2_bddAbove`

English:
theorem BddBelow.image2_bddAbove
  statement: BddBelow s -> BddBelow t -> BddAbove (Set.image2 f s t)
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]

中文:
定理 BddBelow.image2_bddAbove
  结论: BddBelow s -> BddBelow t -> BddAbove (集合.image2 f s t)
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]

Depends on / 依赖: mem_upperBounds_image2_of_mem_lowerBounds
-/
theorem BddBelow.image2_bddAbove : BddBelow s -> BddBelow t -> BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

@[to_dual]
/--
theorem `IsLeast.isGreatest_image2` / 定理 `IsLeast.isGreatest_image2`

English:
theorem IsLeast.isGreatest_image2
  given: (ha : IsLeast s a) (hb : IsLeast t b)
  proof: ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

中文:
定理 IsLeast.isGreatest_image2
  条件: (ha : IsLeast s a) (hb : IsLeast t b)
  证明: ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

Depends on / 依赖: mem_image2_of_mem, mem_upperBounds_image2_of_mem_lowerBounds
-/
theorem IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : forall b, Antitone (swap f b)) (h₁ : forall a, Monotone (f a))

include h₀ h₁

@[to_dual]
/--
theorem `mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds` / 定理 `mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds`

English:
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds
  statement: (ha : a in lowerBounds s)
  proof: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

中文:
定理 mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds
  结论: (ha : a in lowerBounds s)
  证明: forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]

Depends on / 依赖: forall_mem_image2
-/
theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a in lowerBounds s)
    (hb : b in upperBounds t) : f a b in upperBounds (image2 f s t) :=
forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans h₁ _ hb hy

@[to_dual]
/--
theorem `image2_lowerBounds_upperBounds_subset_upperBounds_image2` / 定理 `image2_lowerBounds_upperBounds_subset_upperBounds_image2`

English:
theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2
  proof: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

@[to_dual]

中文:
定理 image2_lowerBounds_upperBounds_subset_upperBounds_image2
  证明: image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

@[to_dual]

Depends on / 依赖: image2_subset_iff, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds
-/
theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) subseteq upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb =>
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

@[to_dual]
/--
theorem `BddBelow.bddAbove_image2_of_bddAbove` / 定理 `BddBelow.bddAbove_image2_of_bddAbove`

English:
theorem BddBelow.bddAbove_image2_of_bddAbove
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

@[to_dual]

中文:
定理 BddBelow.bddAbove_image2_of_bddAbove
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

@[to_dual]

Depends on / 依赖: mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds
-/
theorem BddBelow.bddAbove_image2_of_bddAbove :
    BddBelow s -> BddAbove t -> BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

@[to_dual]
/--
theorem `IsLeast.isGreatest_image2_of_isGreatest` / 定理 `IsLeast.isGreatest_image2_of_isGreatest`

English:
theorem IsLeast.isGreatest_image2_of_isGreatest
  given: (ha : IsLeast s a) (hb : IsGreatest t b)
  proof: ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

中文:
定理 IsLeast.isGreatest_image2_of_isGreatest
  条件: (ha : IsLeast s a) (hb : IsGreatest t b)
  证明: ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

Depends on / 依赖: mem_image2_of_mem, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds
-/
theorem IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneMonotone

end Image2

section IsCofinalFor
variable {α β : Type*} [Preorder α] [Preorder β] {s t : Set α} {f : α -> β}

@[to_dual]
/--
lemma `IsCofinalFor.image_of_monotone` / 引理 `IsCofinalFor.image_of_monotone`

English:
lemma IsCofinalFor.image_of_monotone
  given: (hst : IsCofinalFor s t) (hf : Monotone f)
  proof: by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

@[to_dual]

中文:
引理 IsCofinalFor.image_of_monotone
  条件: (hst : IsCofinalFor s t) (hf : 递增 f)
  证明: by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

@[to_dual]

Depends on / 依赖: IsCofinalFor, exists_mem_image, forall_mem_image
-/
lemma IsCofinalFor.image_of_monotone (hst : IsCofinalFor s t) (hf : Monotone f) :
    IsCofinalFor (f '' s) (f '' t) := by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

@[to_dual]
/--
lemma `IsCofinalFor.image_of_antitone` / 引理 `IsCofinalFor.image_of_antitone`

English:
lemma IsCofinalFor.image_of_antitone
  given: (hst : IsCofinalFor s t) (hf : Antitone f)
  proof: by
  simp only [IsCoinitialFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

中文:
引理 IsCofinalFor.image_of_antitone
  条件: (hst : IsCofinalFor s t) (hf : 递减 f)
  证明: by
  simp only [IsCoinitialFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

Depends on / 依赖: IsCoinitialFor, exists_mem_image, forall_mem_image
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
/--
lemma `bddAbove_prod` / 引理 `bddAbove_prod`

English:
lemma bddAbove_prod
  given: {s : Set (α × β)}
  proof: ⟨fun ⟨p, hp⟩ => ⟨⟨p.1, forall_mem_image.2 fun _q hq => (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq => (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨⟨x, y⟩, fun _p hp =>
⟨hx mem_image_of_mem _ hp, hy mem_image_of_mem _ hp⟩⟩⟩

@[to_dual]

中文:
引理 bddAbove_prod
  条件: {s : 集合 (α × β)}
  证明: ⟨fun ⟨p, hp⟩ => ⟨⟨p.1, forall_mem_image.2 fun _q hq => (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq => (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨⟨x, y⟩, fun _p hp =>
⟨hx mem_image_of_mem _ hp, hy mem_image_of_mem _ hp⟩⟩⟩

@[to_dual]

Depends on / 依赖: forall_mem_image, mem_image_of_mem
-/
lemma bddAbove_prod {s : Set (α × β)} :
    BddAbove s ↔ BddAbove (Prod.fst '' s) ∧ BddAbove (Prod.snd '' s) :=
  ⟨fun ⟨p, hp⟩ => ⟨⟨p.1, forall_mem_image.2 fun _q hq => (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq => (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨⟨x, y⟩, fun _p hp =>
⟨hx mem_image_of_mem _ hp, hy mem_image_of_mem _ hp⟩⟩⟩

@[to_dual]
/--
lemma `bddAbove_range_prod` / 引理 `bddAbove_range_prod`

English:
lemma bddAbove_range_prod
  given: {F : ι -> α × β}
  proof: by
  simp only [bddAbove_prod, ← range_comp]

@[to_dual]

中文:
引理 bddAbove_range_prod
  条件: {F : ι -> α × β}
  证明: by
  simp only [bddAbove_prod, ← range_comp]

@[to_dual]

Depends on / 依赖: bddAbove_prod, range_comp
-/
lemma bddAbove_range_prod {F : ι -> α × β} :
    BddAbove (range F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F) := by
  simp only [bddAbove_prod, ← range_comp]

@[to_dual]
/--
theorem `isLUB_prod` / 定理 `isLUB_prod`

English:
theorem isLUB_prod
  given: {s : Set (α × β)} {p : α × β}
  proof: by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) in upperBounds s from (H.2 h).1
exact fun q hq => ⟨ha mem_image_of_mem _ hq, (H.1 hq).2⟩
  

中文:
定理 isLUB_prod
  条件: {s : 集合 (α × β)} {p : α × β}
  证明: by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) in upperBounds s from (H.2 h).1
exact fun q hq => ⟨ha mem_image_of_mem _ hq, (H.1 hq).2⟩
  

Depends on / 依赖: mem_image_of_mem, mem_upperBounds_image, monotone_fs, monotone_fst, monotone_fst.mem_upperBounds_image, monotone_snd, monotone_snd.mem_upperBounds_image, upperBounds
-/
theorem isLUB_prod {s : Set (α × β)} {p : α × β} :
    IsLUB s p ↔ IsLUB (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2 := by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) in upperBounds s from (H.2 h).1
exact fun q hq => ⟨ha mem_image_of_mem _ hq, (H.1 hq).2⟩
  · suffices h : (p.1, a) in upperBounds s from (H.2 h).2
exact fun q hq => ⟨(H.1 hq).1, ha mem_image_of_mem _ hq⟩
· exact fun q hq => ⟨H.1.1 mem_image_of_mem _ hq, H.2.1 mem_image_of_mem _ hq⟩
  · exact fun q hq =>
⟨H.1.2 monotone_fst.mem_upperBounds_image hq,
H.2.2 monotone_snd.mem_upperBounds_image hq⟩

/--
lemma `Monotone.upperBounds_image_of_directedOn_prod` / 引理 `Monotone.upperBounds_image_of_directedOn_prod`

English:
lemma Monotone.upperBounds_image_of_directedOn_prod
  statement: {γ : Type*} [Preorder γ] {g : α × β -> γ}
  proof: le_antisymm
  (upperBounds_mono_of_isCofinalFor (hd.isCofinalFor_fst_image_prod_snd_image.image_of_monotone hg))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))

中文:
引理 递增.upperBounds_image_of_directedOn_prod
  结论: {γ : 类型} [预序 γ] {g : α × β -> γ}
  证明: le_antisymm
  (upperBounds_mono_of_isCofinalFor (hd.isCofinalFor_fst_image_prod_snd_image.image_of_monotone hg))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))

Depends on / 依赖: le_antisymm
-/
lemma Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β -> γ}
    (hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· <= ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := le_antisymm
  (upperBounds_mono_of_isCofinalFor (hd.isCofinalFor_fst_image_prod_snd_image.image_of_monotone hg))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))

end Prod


section Pi

variable {π : α -> Type*} [forall a, Preorder (π a)]

@[to_dual]
/--
lemma `bddAbove_pi` / 引理 `bddAbove_pi`

English:
lemma bddAbove_pi
  given: {s : Set (forall a, π a)}
  proof: ⟨fun ⟨f, hf⟩ a => ⟨f a, forall_mem_image.2 fun _ hg => hf hg a⟩,
fun h => ⟨fun a => (h a).some, fun _ hg a => (h a).some_mem mem_image_of_mem _ hg⟩⟩

@[to_dual]

中文:
引理 bddAbove_pi
  条件: {s : 集合 (对任意 a, π a)}
  证明: ⟨fun ⟨f, hf⟩ a => ⟨f a, forall_mem_image.2 fun _ hg => hf hg a⟩,
fun h => ⟨fun a => (h a).some, fun _ hg a => (h a).some_mem mem_image_of_mem _ hg⟩⟩

@[to_dual]

Depends on / 依赖: forall_mem_image, mem_image_of_mem, some_mem
-/
lemma bddAbove_pi {s : Set (forall a, π a)} :
    BddAbove s ↔ forall a, BddAbove (Function.eval a '' s) :=
  ⟨fun ⟨f, hf⟩ a => ⟨f a, forall_mem_image.2 fun _ hg => hf hg a⟩,
fun h => ⟨fun a => (h a).some, fun _ hg a => (h a).some_mem mem_image_of_mem _ hg⟩⟩

@[to_dual]
/--
lemma `bddAbove_range_pi` / 引理 `bddAbove_range_pi`

English:
lemma bddAbove_range_pi
  given: {F : ι -> forall a, π a}
  proof: by
  simp only [bddAbove_pi, ← range_comp]
  rfl

@[to_dual]

中文:
引理 bddAbove_range_pi
  条件: {F : ι -> 对任意 a, π a}
  证明: by
  simp only [bddAbove_pi, ← range_comp]
  rfl

@[to_dual]

Depends on / 依赖: bddAbove_pi, range_comp
-/
lemma bddAbove_range_pi {F : ι -> forall a, π a} :
    BddAbove (range F) ↔ forall a, BddAbove (range fun i => F i a) := by
  simp only [bddAbove_pi, ← range_comp]
  rfl

@[to_dual]
/--
theorem `isLUB_pi` / 定理 `isLUB_pi`

English:
theorem isLUB_pi
  given: {s : Set (forall a, π a)} {f : forall a, π a}
  proof: by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b in upperBounds s from Function.update_self a b f ▸ H.2 h a
exact fun g hg => le_update_iff.2 ⟨hb mem_image_of_mem _ 

中文:
定理 isLUB_pi
  条件: {s : 集合 (对任意 a, π a)} {f : 对任意 a, π a}
  证明: by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b in upperBounds s from Function.update_self a b f ▸ H.2 h a
exact fun g hg => le_update_iff.2 ⟨hb mem_image_of_mem _ 

Depends on / 依赖: Function, Function.monotone_eval, Function.update, Function.update_self, classical, le_update_iff, mem_image_of_mem, mem_upperBounds_image, monotone_eval, update, update_self, upperBounds
-/
theorem isLUB_pi {s : Set (forall a, π a)} {f : forall a, π a} :
    IsLUB s f ↔ forall a, IsLUB (Function.eval a '' s) (f a) := by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b in upperBounds s from Function.update_self a b f ▸ H.2 h a
exact fun g hg => le_update_iff.2 ⟨hb mem_image_of_mem _ hg, fun i _ => H.1 hg i⟩
    · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upperBounds_image hg)

end Pi

@[to_dual]
/--
theorem `IsGLB.of_image` / 定理 `IsGLB.of_image`

English:
theorem IsGLB.of_image
  statement: [Preorder α] [Preorder β] {f : α -> β} (hf : forall {x y}, f x <= f y ↔ x <= y)
  proof: ⟨fun _ hy => hf.1 hx.1 mem_image_of_mem _ hy, fun _ hy =>
hf.1 hx.2 Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

@[to_dual (reorder := f g)]

中文:
定理 IsGLB.of_image
  结论: [预序 α] [预序 β] {f : α -> β} (hf : 对任意 {x y}, f x <= f y ↔ x <= y)
  证明: ⟨fun _ hy => hf.1 hx.1 mem_image_of_mem _ hy, fun _ hy =>
hf.1 hx.2 Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

@[to_dual (reorder := f g)]

Depends on / 依赖: Monotone, Monotone.mem_lowerBounds_image, mem_image_of_mem, mem_lowerBounds_image
-/
theorem IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (hf : forall {x y}, f x <= f y ↔ x <= y)
    {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x :=
⟨fun _ hy => hf.1 hx.1 mem_image_of_mem _ hy, fun _ hy =>
hf.1 hx.2 Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

@[to_dual (reorder := f g)]
/--
lemma `BddAbove.range_mono` / 引理 `BddAbove.range_mono`

English:
lemma BddAbove.range_mono
  statement: [Preorder β] {f : α -> β} (g : α -> β) (h : forall a, f a <= g a)
  proof: by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

@[to_dual]

中文:
引理 BddAbove.range_mono
  结论: [预序 β] {f : α -> β} (g : α -> β) (h : 对任意 a, f a <= g a)
  证明: by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

@[to_dual]

Depends on / 依赖: mem_range_self
-/
lemma BddAbove.range_mono [Preorder β] {f : α -> β} (g : α -> β) (h : forall a, f a <= g a)
    (hbdd : BddAbove (range g)) : BddAbove (range f) := by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

@[to_dual]
/--
lemma `BddAbove.range_comp_left` / 引理 `BddAbove.range_comp_left`

English:
lemma BddAbove.range_comp_left
  statement: {γ : Type*} [Preorder β] [Preorder γ] {f : α -> β} {g : β -> γ}
  proof: by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

@[deprecated BddAbove.range_comp_left (since := "2026-06-07")]
alias BddAbove.range_comp := BddAbove.range_comp_left

@[deprecated BddBelow.range_comp_left (since := "2026-06-07")]
alias BddBelow.range_comp 

中文:
引理 BddAbove.range_comp_left
  结论: {γ : 类型} [预序 β] [预序 γ] {f : α -> β} {g : β -> γ}
  证明: by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

@[deprecated BddAbove.range_comp_left (since := "2026-06-07")]
alias BddAbove.range_comp := BddAbove.range_comp_left

@[deprecated BddBelow.range_comp_left (since := "2026-06-07")]
alias BddBelow.range_comp 

Depends on / 依赖: BddAbove, Set.range_comp, hg.map_bddAbove, map_bddAbove, range_comp
-/
lemma BddAbove.range_comp_left {γ : Type*} [Preorder β] [Preorder γ] {f : α -> β} {g : β -> γ}
    (hf : BddAbove (range f)) (hg : Monotone g) : BddAbove (range (fun x => g (f x))) := by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

@[deprecated BddAbove.range_comp_left (since := "2026-06-07")]
alias BddAbove.range_comp := BddAbove.range_comp_left

@[deprecated BddBelow.range_comp_left (since := "2026-06-07")]
alias BddBelow.range_comp := BddBelow.range_comp_left
