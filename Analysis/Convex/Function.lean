/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Tactic.NormNum

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `Analysis.Convex.Integral`.

A function `f : E → β` is `ConvexOn` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `ConvexOn 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `ConvexOn 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `ConcaveOn 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `StrictConvexOn 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `StrictConcaveOn 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/

@[expose] public section

open LinearMap Set Convex Pointwise

variable {𝕜 E F α β ι : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 β] (s : Set E) (f : E -> β) {g : β -> α}

/--
Definition of `ConvexOn` / `ConvexOn` 的定义

English:
definition ConvexOn
  signature: : Prop
  body: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y

中文:
定义 ConvexOn
  签名: : 命题
  定义体: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y

Depends on / 依赖: Convex
-/
def ConvexOn : Prop :=
  Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y

/--
Definition of `ConcaveOn` / `ConcaveOn` 的定义

English:
definition ConcaveOn
  signature: : Prop
  body: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y <= f (a • x + b • y)

中文:
定义 ConcaveOn
  签名: : 命题
  定义体: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y <= f (a • x + b • y)

Depends on / 依赖: Convex
-/
def ConcaveOn : Prop :=
  Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y <= f (a • x + b • y)

/--
Definition of `StrictConvexOn` / `StrictConvexOn` 的定义

English:
definition StrictConvexOn
  signature: : Prop
  body: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    f (a • x + b • y) < a • f x + b • f y

中文:
定义 StrictConvexOn
  签名: : 命题
  定义体: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    f (a • x + b • y) < a • f x + b • f y

Depends on / 依赖: Convex
-/
def StrictConvexOn : Prop :=
  Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    f (a • x + b • y) < a • f x + b • f y

/--
Definition of `StrictConcaveOn` / `StrictConcaveOn` 的定义

English:
definition StrictConcaveOn
  signature: : Prop
  body: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    a • f x + b • f y < f (a • x + b • y)

中文:
定义 StrictConcaveOn
  签名: : 命题
  定义体: Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    a • f x + b • f y < f (a • x + b • y)

Depends on / 依赖: Convex
-/
def StrictConcaveOn : Prop :=
  Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
    a • f x + b • f y < f (a • x + b • y)

variable {𝕜 s f}

open OrderDual (toDual ofDual)

/--
theorem `ConvexOn.dual` / 定理 `ConvexOn.dual`

English:
theorem ConvexOn.dual
  given: (hf : ConvexOn 𝕜 s f)
  statement: ConcaveOn 𝕜 s (toDual ∘ f)
  proof: hf

中文:
定理 ConvexOn.dual
  条件: (hf : ConvexOn 𝕜 s f)
  结论: ConcaveOn 𝕜 s (toDual ∘ f)
  证明: hf
-/
theorem ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDual ∘ f) := hf

/--
theorem `ConcaveOn.dual` / 定理 `ConcaveOn.dual`

English:
theorem ConcaveOn.dual
  given: (hf : ConcaveOn 𝕜 s f)
  statement: ConvexOn 𝕜 s (toDual ∘ f)
  proof: hf

中文:
定理 ConcaveOn.dual
  条件: (hf : ConcaveOn 𝕜 s f)
  结论: ConvexOn 𝕜 s (toDual ∘ f)
  证明: hf
-/
theorem ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (toDual ∘ f) := hf

/--
theorem `StrictConvexOn.dual` / 定理 `StrictConvexOn.dual`

English:
theorem StrictConvexOn.dual
  given: (hf : StrictConvexOn 𝕜 s f)
  statement: StrictConcaveOn 𝕜 s (toDual ∘ f)
  proof: hf

中文:
定理 StrictConvexOn.dual
  条件: (hf : StrictConvexOn 𝕜 s f)
  结论: StrictConcaveOn 𝕜 s (toDual ∘ f)
  证明: hf
-/
theorem StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (toDual ∘ f) := hf

/--
theorem `StrictConcaveOn.dual` / 定理 `StrictConcaveOn.dual`

English:
theorem StrictConcaveOn.dual
  given: (hf : StrictConcaveOn 𝕜 s f)
  statement: StrictConvexOn 𝕜 s (toDual ∘ f)
  proof: hf

中文:
定理 StrictConcaveOn.dual
  条件: (hf : StrictConcaveOn 𝕜 s f)
  结论: StrictConvexOn 𝕜 s (toDual ∘ f)
  证明: hf
-/
theorem StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (toDual ∘ f) := hf

/--
theorem `convexOn_id` / 定理 `convexOn_id`

English:
theorem convexOn_id
  given: {s : Set β} (hs : Convex 𝕜 s)
  statement: ConvexOn 𝕜 s _root_.id
  proof: ⟨hs, by
    intros
    rfl⟩

中文:
定理 convexOn_id
  条件: {s : 集合 β} (hs : 凸 𝕜 s)
  结论: ConvexOn 𝕜 s _root_.id
  证明: ⟨hs, by
    intros
    rfl⟩

Depends on / 依赖: intros
-/
theorem convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

/--
theorem `concaveOn_id` / 定理 `concaveOn_id`

English:
theorem concaveOn_id
  given: {s : Set β} (hs : Convex 𝕜 s)
  statement: ConcaveOn 𝕜 s _root_.id
  proof: ⟨hs, by
    intros
    rfl⟩

中文:
定理 concaveOn_id
  条件: {s : 集合 β} (hs : 凸 𝕜 s)
  结论: ConcaveOn 𝕜 s _root_.id
  证明: ⟨hs, by
    intros
    rfl⟩

Depends on / 依赖: intros
-/
theorem concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

section congr

variable {g : E -> β}

/--
theorem `ConvexOn.congr` / 定理 `ConvexOn.congr`

English:
theorem ConvexOn.congr
  given: (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s)
  statement: ConvexOn 𝕜 s g
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

中文:
定理 ConvexOn.congr
  条件: (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s)
  结论: ConvexOn 𝕜 s g
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩
-/
theorem ConvexOn.congr (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s) : ConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

/--
theorem `ConcaveOn.congr` / 定理 `ConcaveOn.congr`

English:
theorem ConcaveOn.congr
  given: (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s)
  statement: ConcaveOn 𝕜 s g
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

中文:
定理 ConcaveOn.congr
  条件: (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s)
  结论: ConcaveOn 𝕜 s g
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩
-/
theorem ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s) : ConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

/--
theorem `StrictConvexOn.congr` / 定理 `StrictConvexOn.congr`

English:
theorem StrictConvexOn.congr
  given: (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s)
  proof: ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

中文:
定理 StrictConvexOn.congr
  条件: (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s)
  证明: ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

Depends on / 依赖: ha.le, hb.le
-/
theorem StrictConvexOn.congr (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

/--
theorem `StrictConcaveOn.congr` / 定理 `StrictConcaveOn.congr`

English:
theorem StrictConcaveOn.congr
  given: (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s)
  proof: ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

中文:
定理 StrictConcaveOn.congr
  条件: (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s)
  证明: ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

Depends on / 依赖: ha.le, hb.le
-/
theorem StrictConcaveOn.congr (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

end congr

/--
theorem `ConvexOn.subset` / 定理 `ConvexOn.subset`

English:
theorem ConvexOn.subset
  given: {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s subseteq t) (hs : Convex 𝕜 s)
  proof: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

中文:
定理 ConvexOn.subset
  条件: {t : 集合 E} (hf : ConvexOn 𝕜 t f) (hst : s subseteq t) (hs : 凸 𝕜 s)
  证明: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
-/
theorem ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s subseteq t) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

/--
theorem `ConcaveOn.subset` / 定理 `ConcaveOn.subset`

English:
theorem ConcaveOn.subset
  given: {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s subseteq t) (hs : Convex 𝕜 s)
  proof: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

中文:
定理 ConcaveOn.subset
  条件: {t : 集合 E} (hf : ConcaveOn 𝕜 t f) (hst : s subseteq t) (hs : 凸 𝕜 s)
  证明: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
-/
theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s subseteq t) (hs : Convex 𝕜 s) :
    ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

/--
theorem `StrictConvexOn.subset` / 定理 `StrictConvexOn.subset`

English:
theorem StrictConvexOn.subset
  statement: {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s subseteq t)
  proof: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

中文:
定理 StrictConvexOn.subset
  结论: {t : 集合 E} (hf : StrictConvexOn 𝕜 t f) (hst : s subseteq t)
  证明: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
-/
theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s subseteq t)
    (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

/--
theorem `StrictConcaveOn.subset` / 定理 `StrictConcaveOn.subset`

English:
theorem StrictConcaveOn.subset
  statement: {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s subseteq t)
  proof: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

中文:
定理 StrictConcaveOn.subset
  结论: {t : 集合 E} (hf : StrictConcaveOn 𝕜 t f) (hst : s subseteq t)
  证明: ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
-/
theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s subseteq t)
    (hs : Convex 𝕜 s) : StrictConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

/--
theorem `ConvexOn.comp` / 定理 `ConvexOn.comp`

English:
theorem ConvexOn.comp
  statement: (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  proof: ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩

中文:
定理 ConvexOn.comp
  结论: (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  证明: ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩

Depends on / 依赖: mem_image_of_mem
-/
theorem ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩

/--
theorem `ConcaveOn.comp` / 定理 `ConcaveOn.comp`

English:
theorem ConcaveOn.comp
  statement: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  proof: ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
(hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
(mem_image_of_mem f <| hf.1 hx hy ha hb hab)
        hf.2 hx hy ha hb hab⟩

中文:
定理 ConcaveOn.comp
  结论: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  证明: ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
(hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
(mem_image_of_mem f <| hf.1 hx hy ha hb hab)
        hf.2 hx hy ha hb hab⟩

Depends on / 依赖: mem_image_of_mem
-/
theorem ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
(hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
(mem_image_of_mem f <| hf.1 hx hy ha hb hab)
        hf.2 hx hy ha hb hab⟩

/--
theorem `ConvexOn.comp_concaveOn` / 定理 `ConvexOn.comp_concaveOn`

English:
theorem ConvexOn.comp_concaveOn
  statement: (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  proof: hg.dual.comp hf hg'

中文:
定理 ConvexOn.comp_concaveOn
  结论: (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  证明: hg.dual.comp hf hg'

Depends on / 依赖: hg.dual.comp
-/
theorem ConvexOn.comp_concaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

/--
theorem `ConcaveOn.comp_convexOn` / 定理 `ConcaveOn.comp_convexOn`

English:
theorem ConcaveOn.comp_convexOn
  statement: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  proof: hg.dual.comp hf hg'

中文:
定理 ConcaveOn.comp_convexOn
  结论: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  证明: hg.dual.comp hf hg'

Depends on / 依赖: hg.dual.comp
-/
theorem ConcaveOn.comp_convexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

/--
theorem `StrictConvexOn.comp` / 定理 `StrictConvexOn.comp`

English:
theorem StrictConvexOn.comp
  statement: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  proof: ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab)
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩

中文:
定理 StrictConvexOn.comp
  结论: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  证明: ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab)
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩

Depends on / 依赖: ha.le, hb.le, mem_image_of_mem
-/
theorem StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
(hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab)
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩

/--
theorem `StrictConcaveOn.comp_strictConvexOn` / 定理 `StrictConcaveOn.comp_strictConvexOn`

English:
theorem StrictConcaveOn.comp_strictConvexOn
  statement: (hg : StrictConcaveOn 𝕜 (f '' s) g)
  proof: hg.dual.comp hf hg' hf'

中文:
定理 StrictConcaveOn.comp_strictConvexOn
  结论: (hg : StrictConcaveOn 𝕜 (f '' s) g)
  证明: hg.dual.comp hf hg' hf'

Depends on / 依赖: hg.dual.comp
-/
theorem StrictConcaveOn.comp_strictConvexOn (hg : StrictConcaveOn 𝕜 (f '' s) g)
    (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

/--
theorem `StrictConcaveOn.comp` / 定理 `StrictConcaveOn.comp`

English:
theorem StrictConcaveOn.comp
  statement: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  proof: hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual hf'

中文:
定理 StrictConcaveOn.comp
  结论: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  证明: hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual hf'

Depends on / 依赖: comp_strictConvexOn, hg.comp_strictConvexOn
-/
theorem StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual hf'

/--
theorem `StrictConvexOn.comp_strictConcaveOn` / 定理 `StrictConvexOn.comp_strictConcaveOn`

English:
theorem StrictConvexOn.comp_strictConcaveOn
  statement: (hg : StrictConvexOn 𝕜 (f '' s) g)
  proof: hg.dual.comp hf hg' hf'

中文:
定理 StrictConvexOn.comp_strictConcaveOn
  结论: (hg : StrictConvexOn 𝕜 (f '' s) g)
  证明: hg.dual.comp hf hg' hf'

Depends on / 依赖: hg.dual.comp
-/
theorem StrictConvexOn.comp_strictConcaveOn (hg : StrictConvexOn 𝕜 (f '' s) g)
    (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

/--
theorem `ConvexOn.comp_strictConvexOn` / 定理 `ConvexOn.comp_strictConvexOn`

English:
theorem ConvexOn.comp_strictConvexOn
  statement: (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  proof: by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le (b := g (a • f x + b • f y)) ?_ ?_⟩
· refine hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) ?_ hf.2 hx hy hxy ha hb hab
    exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

中文:
定理 ConvexOn.comp_strictConvexOn
  结论: (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  证明: by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le (b := g (a • f x + b • f y)) ?_ ?_⟩
· refine hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) ?_ hf.2 hx hy hxy ha hb hab
    exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

Depends on / 依赖: ha.le, hb.le, hf.left, hg.left, hg.right, mem_image_of_mem, trans_le
-/
theorem ConvexOn.comp_strictConvexOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f) := by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le (b := g (a • f x + b • f y)) ?_ ?_⟩
· refine hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) ?_ hf.2 hx hy hxy ha hb hab
    exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

/--
theorem `ConcaveOn.comp_strictConvexOn` / 定理 `ConcaveOn.comp_strictConvexOn`

English:
theorem ConcaveOn.comp_strictConvexOn
  statement: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  proof: hg.dual.comp_strictConvexOn hf hg'

中文:
定理 ConcaveOn.comp_strictConvexOn
  结论: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
  证明: hg.dual.comp_strictConvexOn hf hg'

Depends on / 依赖: comp_strictConvexOn, hg.dual.comp_strictConvexOn
-/
theorem ConcaveOn.comp_strictConvexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictAntiOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_strictConvexOn hf hg'

/--
theorem `ConcaveOn.comp_strictConcaveOn` / 定理 `ConcaveOn.comp_strictConcaveOn`

English:
theorem ConcaveOn.comp_strictConcaveOn
  statement: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  proof: hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual

中文:
定理 ConcaveOn.comp_strictConcaveOn
  结论: (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  证明: hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual

Depends on / 依赖: comp_strictConvexOn, hg.comp_strictConvexOn
-/
theorem ConcaveOn.comp_strictConcaveOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual

/--
theorem `ConvexOn.comp_strictConcaveOn` / 定理 `ConvexOn.comp_strictConcaveOn`

English:
theorem ConvexOn.comp_strictConcaveOn
  statement: (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  proof: hg.dual.comp_strictConcaveOn hf hg'

中文:
定理 ConvexOn.comp_strictConcaveOn
  结论: (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
  证明: hg.dual.comp_strictConcaveOn hf hg'

Depends on / 依赖: comp_strictConcaveOn, hg.dual.comp_strictConcaveOn
-/
theorem ConvexOn.comp_strictConcaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictAntiOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_strictConcaveOn hf hg'

/--
theorem `StrictConvexOn.comp_convexOn` / 定理 `StrictConvexOn.comp_convexOn`

English:
theorem StrictConvexOn.comp_convexOn
  statement: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  proof: by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le' (b := g (a • f x + b • f y)) ?_ ?_⟩
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) (hf'.ne hx hy hxy) ha hb hab
· refine hg' ?_ ?_ hf.right hx hy ha.le hb.le hab
· exact mem_image_of_mem f hf.left hx hy ha.le hb.le hab
    · exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

中文:
定理 StrictConvexOn.comp_convexOn
  结论: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  证明: by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le' (b := g (a • f x + b • f y)) ?_ ?_⟩
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) (hf'.ne hx hy hxy) ha hb hab
· refine hg' ?_ ?_ hf.right hx hy ha.le hb.le hab
· exact mem_image_of_mem f hf.left hx hy ha.le hb.le hab
    · exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

Depends on / 依赖: ha.le, hb.le, hf.left, hf.right, hg.left, hg.right, mem_image_of_mem, trans_le
-/
theorem StrictConvexOn.comp_convexOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) := by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab => .trans_le' (b := g (a • f x + b • f y)) ?_ ?_⟩
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) (hf'.ne hx hy hxy) ha hb hab
· refine hg' ?_ ?_ hf.right hx hy ha.le hb.le hab
· exact mem_image_of_mem f hf.left hx hy ha.le hb.le hab
    · exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab

/--
theorem `StrictConcaveOn.comp_convexOn` / 定理 `StrictConcaveOn.comp_convexOn`

English:
theorem StrictConcaveOn.comp_convexOn
  statement: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  proof: hg.dual.comp_convexOn hf hg' hf'

中文:
定理 StrictConcaveOn.comp_convexOn
  结论: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  证明: hg.dual.comp_convexOn hf hg' hf'

Depends on / 依赖: comp_convexOn, hg.dual.comp_convexOn
-/
theorem StrictConcaveOn.comp_convexOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_convexOn hf hg' hf'

/--
theorem `StrictConvexOn.comp_concaveOn` / 定理 `StrictConvexOn.comp_concaveOn`

English:
theorem StrictConvexOn.comp_concaveOn
  statement: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  proof: hg.comp_convexOn (β := βᵒᵈ) hf hg'.dual hf'

中文:
定理 StrictConvexOn.comp_concaveOn
  结论: (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  证明: hg.comp_convexOn (β := βᵒᵈ) hf hg'.dual hf'

Depends on / 依赖: comp_convexOn, hg.comp_convexOn
-/
theorem StrictConvexOn.comp_concaveOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.comp_convexOn (β := βᵒᵈ) hf hg'.dual hf'

/--
theorem `StrictConcaveOn.comp_concaveOn` / 定理 `StrictConcaveOn.comp_concaveOn`

English:
theorem StrictConcaveOn.comp_concaveOn
  statement: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  proof: hg.dual.comp_concaveOn hf hg' hf'

中文:
定理 StrictConcaveOn.comp_concaveOn
  结论: (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
  证明: hg.dual.comp_concaveOn hf hg' hf'

Depends on / 依赖: comp_concaveOn, hg.dual.comp_concaveOn
-/
theorem StrictConcaveOn.comp_concaveOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_concaveOn hf hg' hf'

end SMul

section DistribMulAction

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E -> β}

/--
theorem `ConvexOn.add` / 定理 `ConvexOn.add`

English:
theorem ConvexOn.add
  given: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  statement: ConvexOn 𝕜 s (f + g)
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) <= a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩

中文:
定理 ConvexOn.add
  条件: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  结论: ConvexOn 𝕜 s (f + g)
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) <= a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩

Depends on / 依赖: add_add_add_comm, add_le_add, smul_add
-/
theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) <= a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩

/--
theorem `ConcaveOn.add` / 定理 `ConcaveOn.add`

English:
theorem ConcaveOn.add
  given: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  statement: ConcaveOn 𝕜 s (f + g)
  proof: hf.dual.add hg

中文:
定理 ConcaveOn.add
  条件: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  结论: ConcaveOn 𝕜 s (f + g)
  证明: hf.dual.add hg

Depends on / 依赖: hf.dual.add
-/
theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `convexOn_const` / 定理 `convexOn_const`

English:
theorem convexOn_const
  given: (c : β) (hs : Convex 𝕜 s)
  statement: ConvexOn 𝕜 s fun _ : E => c
  proof: ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩

中文:
定理 convexOn_const
  条件: (c : β) (hs : 凸 𝕜 s)
  结论: ConvexOn 𝕜 s fun _ : E => c
  证明: ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩

Depends on / 依赖: Convex, Convex.combo_self, combo_self
-/
theorem convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun _ : E => c :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩

/--
theorem `concaveOn_const` / 定理 `concaveOn_const`

English:
theorem concaveOn_const
  given: (c : β) (hs : Convex 𝕜 s)
  statement: ConcaveOn 𝕜 s fun _ => c
  proof: convexOn_const (β := βᵒᵈ) _ hs

中文:
定理 concaveOn_const
  条件: (c : β) (hs : 凸 𝕜 s)
  结论: ConcaveOn 𝕜 s fun _ => c
  证明: convexOn_const (β := βᵒᵈ) _ hs

Depends on / 依赖: convexOn_const
-/
theorem concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun _ => c :=
  convexOn_const (β := βᵒᵈ) _ hs

/--
theorem `ConvexOn.add_const` / 定理 `ConvexOn.add_const`

English:
theorem ConvexOn.add_const
  given: [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β)
  proof: hf.add (convexOn_const _ hf.1)

中文:
定理 ConvexOn.add_const
  条件: [是OrderedAdd幺半群 β] (hf : ConvexOn 𝕜 s f) (b : β)
  证明: hf.add (convexOn_const _ hf.1)

Depends on / 依赖: convexOn_const, hf.add
-/
theorem ConvexOn.add_const [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β) :
    ConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add (convexOn_const _ hf.1)

/--
theorem `ConcaveOn.add_const` / 定理 `ConcaveOn.add_const`

English:
theorem ConcaveOn.add_const
  given: [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β)
  proof: hf.add (concaveOn_const _ hf.1)

中文:
定理 ConcaveOn.add_const
  条件: [是OrderedAdd幺半群 β] (hf : ConcaveOn 𝕜 s f) (b : β)
  证明: hf.add (concaveOn_const _ hf.1)

Depends on / 依赖: concaveOn_const, hf.add
-/
theorem ConcaveOn.add_const [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β) :
    ConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add (concaveOn_const _ hf.1)

/--
theorem `convexOn_of_convex_epigraph` / 定理 `convexOn_of_convex_epigraph`

English:
theorem convexOn_of_convex_epigraph
  given: (h : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 })
  proof: ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

中文:
定理 convexOn_of_convex_epigraph
  条件: (h : 凸 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 })
  证明: ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

Depends on / 依赖: le_rfl
-/
theorem convexOn_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }) :
    ConvexOn 𝕜 s f :=
  ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

/--
theorem `concaveOn_of_convex_hypograph` / 定理 `concaveOn_of_convex_hypograph`

English:
theorem concaveOn_of_convex_hypograph
  given: (h : Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 })
  proof: convexOn_of_convex_epigraph (β := βᵒᵈ) h

中文:
定理 concaveOn_of_convex_hypograph
  条件: (h : 凸 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 })
  证明: convexOn_of_convex_epigraph (β := βᵒᵈ) h

Depends on / 依赖: convexOn_of_convex_epigraph
-/
theorem concaveOn_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 }) :
    ConcaveOn 𝕜 s f :=
  convexOn_of_convex_epigraph (β := βᵒᵈ) h

end Module

section PosSMulMono

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `ConvexOn.convex_le` / 定理 `ConvexOn.convex_le`

English:
theorem ConvexOn.convex_le
  given: (hf : ConvexOn 𝕜 s f) (r : β)
  statement: Convex 𝕜 ({ x in s | f x <= r })
  proof: fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ <= a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩

中文:
定理 ConvexOn.convex_le
  条件: (hf : ConvexOn 𝕜 s f) (r : β)
  结论: 凸 𝕜 ({ x in s | f x <= r })
  证明: fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ <= a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩

Depends on / 依赖: Convex, Convex.combo_self, combo_self
-/
theorem ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | f x <= r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ <= a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩

/--
theorem `ConcaveOn.convex_ge` / 定理 `ConcaveOn.convex_ge`

English:
theorem ConcaveOn.convex_ge
  given: (hf : ConcaveOn 𝕜 s f) (r : β)
  statement: Convex 𝕜 ({ x in s | r <= f x })
  proof: hf.dual.convex_le r

中文:
定理 ConcaveOn.convex_ge
  条件: (hf : ConcaveOn 𝕜 s f) (r : β)
  结论: 凸 𝕜 ({ x in s | r <= f x })
  证明: hf.dual.convex_le r

Depends on / 依赖: convex_le, hf.dual.convex_le
-/
theorem ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | r <= f x }) :=
  hf.dual.convex_le r

/--
theorem `ConvexOn.convex_epigraph` / 定理 `ConvexOn.convex_epigraph`

English:
theorem ConvexOn.convex_epigraph
  given: (hf : ConvexOn 𝕜 s f)
  proof: by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • r + b • t := by gcongr

中文:
定理 ConvexOn.convex_epigraph
  条件: (hf : ConvexOn 𝕜 s f)
  证明: by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • r + b • t := by gcongr
-/
theorem ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 } := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • r + b • t := by gcongr

/--
theorem `ConcaveOn.convex_hypograph` / 定理 `ConcaveOn.convex_hypograph`

English:
theorem ConcaveOn.convex_hypograph
  given: (hf : ConcaveOn 𝕜 s f)
  proof: hf.dual.convex_epigraph

中文:
定理 ConcaveOn.convex_hypograph
  条件: (hf : ConcaveOn 𝕜 s f)
  证明: hf.dual.convex_epigraph

Depends on / 依赖: convex_epigraph, hf.dual.convex_epigraph
-/
theorem ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 } :=
  hf.dual.convex_epigraph

/--
theorem `convexOn_iff_convex_epigraph` / 定理 `convexOn_iff_convex_epigraph`

English:
theorem convexOn_iff_convex_epigraph
  proof: ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩

中文:
定理 convexOn_iff_convex_epigraph
  证明: ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩

Depends on / 依赖: ConvexOn, ConvexOn.convex_epigraph, convexOn_of_convex_epigraph, convex_epigraph
-/
theorem convexOn_iff_convex_epigraph :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 } :=
  ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩

/--
theorem `concaveOn_iff_convex_hypograph` / 定理 `concaveOn_iff_convex_hypograph`

English:
theorem concaveOn_iff_convex_hypograph
  proof: convexOn_iff_convex_epigraph (β := βᵒᵈ)

中文:
定理 concaveOn_iff_convex_hypograph
  证明: convexOn_iff_convex_epigraph (β := βᵒᵈ)

Depends on / 依赖: convexOn_iff_convex_epigraph
-/
theorem concaveOn_iff_convex_hypograph :
    ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 } :=
  convexOn_iff_convex_epigraph (β := βᵒᵈ)

end PosSMulMono

section Module

variable [Module 𝕜 E] [SMul 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `ConvexOn.translate_right` / 定理 `ConvexOn.translate_right`

English:
theorem ConvexOn.translate_right
  given: (hf : ConvexOn 𝕜 s f) (c : E)
  proof: ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ <= a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

中文:
定理 ConvexOn.translate_right
  条件: (hf : ConvexOn 𝕜 s f) (c : E)
  证明: ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ <= a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

Depends on / 依赖: Convex, Convex.combo_self, add_add_add_comm, combo_self, smul_add, translate_preimage_right
-/
theorem ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ <= a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

/--
theorem `ConcaveOn.translate_right` / 定理 `ConcaveOn.translate_right`

English:
theorem ConcaveOn.translate_right
  given: (hf : ConcaveOn 𝕜 s f) (c : E)
  proof: hf.dual.translate_right _

中文:
定理 ConcaveOn.translate_right
  条件: (hf : ConcaveOn 𝕜 s f) (c : E)
  证明: hf.dual.translate_right _

Depends on / 依赖: hf.dual.translate_right, translate_right
-/
theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/--
theorem `ConvexOn.translate_left` / 定理 `ConvexOn.translate_left`

English:
theorem ConvexOn.translate_left
  given: (hf : ConvexOn 𝕜 s f) (c : E)
  proof: by
  simpa only [add_comm c] using hf.translate_right c

中文:
定理 ConvexOn.translate_left
  条件: (hf : ConvexOn 𝕜 s f) (c : E)
  证明: by
  simpa only [add_comm c] using hf.translate_right c

Depends on / 依赖: add_comm, hf.translate_right, translate_right
-/
theorem ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm c] using hf.translate_right c

/--
theorem `ConcaveOn.translate_left` / 定理 `ConcaveOn.translate_left`

English:
theorem ConcaveOn.translate_left
  given: (hf : ConcaveOn 𝕜 s f) (c : E)
  proof: hf.dual.translate_left _

中文:
定理 ConcaveOn.translate_left
  条件: (hf : ConcaveOn 𝕜 s f) (c : E)
  证明: hf.dual.translate_left _

Depends on / 依赖: hf.dual.translate_left, translate_left
-/
theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 β]

/--
theorem `convexOn_iff_forall_pos` / 定理 `convexOn_iff_forall_pos`

English:
theorem convexOn_iff_forall_pos
  given: {s : Set E} {f : E -> β}
  proof: by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab

中文:
定理 convexOn_iff_对任意_pos
  条件: {s : 集合 E} {f : E -> β}
  证明: by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab

Depends on / 依赖: add_zero, and_congr_right, eq_or_lt, ha.eq_or_lt, ha.le, hb.eq_or_lt, hb.le, le_rfl, one_smul, simp_rw, zero_add, zero_smul
-/
theorem convexOn_iff_forall_pos {s : Set E} {f : E -> β} :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b ->
      a + b = 1 -> f (a • x + b • y) <= a • f x + b • f y := by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab

/--
theorem `concaveOn_iff_forall_pos` / 定理 `concaveOn_iff_forall_pos`

English:
theorem concaveOn_iff_forall_pos
  given: {s : Set E} {f : E -> β}
  proof: convexOn_iff_forall_pos (β := βᵒᵈ)

中文:
定理 concaveOn_iff_对任意_pos
  条件: {s : 集合 E} {f : E -> β}
  证明: convexOn_iff_forall_pos (β := βᵒᵈ)

Depends on / 依赖: convexOn_iff_forall_pos
-/
theorem concaveOn_iff_forall_pos {s : Set E} {f : E -> β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
        a • f x + b • f y <= f (a • x + b • y) :=
  convexOn_iff_forall_pos (β := βᵒᵈ)

/--
theorem `convexOn_iff_pairwise_pos` / 定理 `convexOn_iff_pairwise_pos`

English:
theorem convexOn_iff_pairwise_pos
  given: {s : Set E} {f : E -> β}
  proof: by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab

中文:
定理 convexOn_iff_pairwise_pos
  条件: {s : 集合 E} {f : E -> β}
  证明: by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab

Depends on / 依赖: Convex, Convex.combo_self, and_congr_right, combo_self, convexOn_iff_forall_pos, eq_or_ne
-/
theorem convexOn_iff_pairwise_pos {s : Set E} {f : E -> β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> f (a • x + b • y) <= a • f x + b • f y := by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab

/--
theorem `concaveOn_iff_pairwise_pos` / 定理 `concaveOn_iff_pairwise_pos`

English:
theorem concaveOn_iff_pairwise_pos
  given: {s : Set E} {f : E -> β}
  proof: convexOn_iff_pairwise_pos (β := βᵒᵈ)

中文:
定理 concaveOn_iff_pairwise_pos
  条件: {s : 集合 E} {f : E -> β}
  证明: convexOn_iff_pairwise_pos (β := βᵒᵈ)

Depends on / 依赖: convexOn_iff_pairwise_pos
-/
theorem concaveOn_iff_pairwise_pos {s : Set E} {f : E -> β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • f x + b • f y <= f (a • x + b • y) :=
  convexOn_iff_pairwise_pos (β := βᵒᵈ)

/--
theorem `LinearMap.convexOn` / 定理 `LinearMap.convexOn`

English:
theorem LinearMap.convexOn
  given: (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s)
  statement: ConvexOn 𝕜 s f
  proof: ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

中文:
定理 线性映射.convexOn
  条件: (f : E ->ₗ[𝕜] β) {s : 集合 E} (hs : 凸 𝕜 s)
  结论: ConvexOn 𝕜 s f
  证明: ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

Depends on / 依赖: f.map_add, f.map_smul, map_add, map_smul
-/
theorem LinearMap.convexOn (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

/--
theorem `LinearMap.concaveOn` / 定理 `LinearMap.concaveOn`

English:
theorem LinearMap.concaveOn
  given: (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s)
  statement: ConcaveOn 𝕜 s f
  proof: ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

中文:
定理 线性映射.concaveOn
  条件: (f : E ->ₗ[𝕜] β) {s : 集合 E} (hs : 凸 𝕜 s)
  结论: ConcaveOn 𝕜 s f
  证明: ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

Depends on / 依赖: f.map_add, f.map_smul, map_add, map_smul
-/
theorem LinearMap.concaveOn (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

/--
theorem `StrictConvexOn.convexOn` / 定理 `StrictConvexOn.convexOn`

English:
theorem StrictConvexOn.convexOn
  given: {s : Set E} {f : E -> β} (hf : StrictConvexOn 𝕜 s f)
  proof: convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

中文:
定理 StrictConvexOn.convexOn
  条件: {s : 集合 E} {f : E -> β} (hf : StrictConvexOn 𝕜 s f)
  证明: convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

Depends on / 依赖: convexOn_iff_pairwise_pos, convexOn_iff_pairwise_pos.mpr
-/
theorem StrictConvexOn.convexOn {s : Set E} {f : E -> β} (hf : StrictConvexOn 𝕜 s f) :
    ConvexOn 𝕜 s f :=
  convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

/--
theorem `StrictConcaveOn.concaveOn` / 定理 `StrictConcaveOn.concaveOn`

English:
theorem StrictConcaveOn.concaveOn
  given: {s : Set E} {f : E -> β} (hf : StrictConcaveOn 𝕜 s f)
  proof: hf.dual.convexOn

中文:
定理 StrictConcaveOn.concaveOn
  条件: {s : 集合 E} {f : E -> β} (hf : StrictConcaveOn 𝕜 s f)
  证明: hf.dual.convexOn

Depends on / 依赖: convexOn, hf.dual.convexOn
-/
theorem StrictConcaveOn.concaveOn {s : Set E} {f : E -> β} (hf : StrictConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s f :=
  hf.dual.convexOn

section PosSMulMono

variable [IsOrderedAddMonoid β] [PosSMulMono 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `StrictConvexOn.convex_lt` / 定理 `StrictConvexOn.convex_lt`

English:
theorem StrictConvexOn.convex_lt
  given: (hf : StrictConvexOn 𝕜 s f) (r : β)
  proof: convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ <= a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩

中文:
定理 StrictConvexOn.convex_lt
  条件: (hf : StrictConvexOn 𝕜 s f) (r : β)
  证明: convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ <= a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩

Depends on / 依赖: Convex, Convex.combo_self, combo_self, convex_iff_pairwise_pos, ha.le, hb.le
-/
theorem StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x in s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ <= a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩

/--
theorem `StrictConcaveOn.convex_gt` / 定理 `StrictConcaveOn.convex_gt`

English:
theorem StrictConcaveOn.convex_gt
  given: (hf : StrictConcaveOn 𝕜 s f) (r : β)
  proof: hf.dual.convex_lt r

中文:
定理 StrictConcaveOn.convex_gt
  条件: (hf : StrictConcaveOn 𝕜 s f) (r : β)
  证明: hf.dual.convex_lt r

Depends on / 依赖: convex_lt, hf.dual.convex_lt
-/
theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x in s | r < f x }) :=
  hf.dual.convex_lt r

end PosSMulMono

section LinearOrder

variable [LinearOrder E] {s : Set E} {f : E -> β}

/--
theorem `LinearOrder.convexOn_of_lt` / 定理 `LinearOrder.convexOn_of_lt`

English:
theorem LinearOrder.convexOn_of_lt
  statement: (hs : Convex 𝕜 s)
  proof: by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

中文:
定理 线性序.convexOn_of_lt
  结论: (hs : 凸 𝕜 s)
  证明: by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

Depends on / 依赖: add_comm, convexOn_iff_pairwise_pos, hxy.lt_or_gt.resolve_left, hxy.symm, lt_or_gt, resolve_left
-/
theorem LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s)
    (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
      f (a • x + b • y) <= a • f x + b • f y) :
    ConvexOn 𝕜 s f := by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/--
theorem `LinearOrder.concaveOn_of_lt` / 定理 `LinearOrder.concaveOn_of_lt`

English:
theorem LinearOrder.concaveOn_of_lt
  statement: (hs : Convex 𝕜 s)
  proof: LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

中文:
定理 线性序.concaveOn_of_lt
  结论: (hs : 凸 𝕜 s)
  证明: LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

Depends on / 依赖: LinearOrder, LinearOrder.convexOn_of_lt, convexOn_of_lt
-/
theorem LinearOrder.concaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
      a • f x + b • f y <= f (a • x + b • y)) :
    ConcaveOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

/--
theorem `LinearOrder.strictConvexOn_of_lt` / 定理 `LinearOrder.strictConvexOn_of_lt`

English:
theorem LinearOrder.strictConvexOn_of_lt
  statement: (hs : Convex 𝕜 s)
  proof: by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

中文:
定理 线性序.strictConvexOn_of_lt
  结论: (hs : 凸 𝕜 s)
  证明: by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

Depends on / 依赖: add_comm, hxy.lt_or_gt.resolve_left, hxy.symm, lt_or_gt, resolve_left
-/
theorem LinearOrder.strictConvexOn_of_lt (hs : Convex 𝕜 s)
    (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
      f (a • x + b • y) < a • f x + b • f y) :
    StrictConvexOn 𝕜 s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/--
theorem `LinearOrder.strictConcaveOn_of_lt` / 定理 `LinearOrder.strictConcaveOn_of_lt`

English:
theorem LinearOrder.strictConcaveOn_of_lt
  statement: (hs : Convex 𝕜 s)
  proof: LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

中文:
定理 线性序.strictConcaveOn_of_lt
  结论: (hs : 凸 𝕜 s)
  证明: LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

Depends on / 依赖: LinearOrder, LinearOrder.strictConvexOn_of_lt, strictConvexOn_of_lt
-/
theorem LinearOrder.strictConcaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
      a • f x + b • f y < f (a • x + b • y)) :
    StrictConcaveOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

end LinearOrder

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/--
theorem `ConvexOn.comp_linearMap` / 定理 `ConvexOn.comp_linearMap`

English:
theorem ConvexOn.comp_linearMap
  given: {f : F -> β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E ->ₗ[𝕜] F)
  proof: ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

中文:
定理 ConvexOn.comp_linearMap
  条件: {f : F -> β} {s : 集合 F} (hf : ConvexOn 𝕜 s f) (g : E ->ₗ[𝕜] F)
  证明: ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

Depends on / 依赖: g.map_add, g.map_smul, linear_preimage, map_add, map_smul
-/
theorem ConvexOn.comp_linearMap {f : F -> β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E ->ₗ[𝕜] F) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/--
theorem `ConcaveOn.comp_linearMap` / 定理 `ConcaveOn.comp_linearMap`

English:
theorem ConcaveOn.comp_linearMap
  given: {f : F -> β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E ->ₗ[𝕜] F)
  proof: hf.dual.comp_linearMap g

中文:
定理 ConcaveOn.comp_linearMap
  条件: {f : F -> β} {s : 集合 F} (hf : ConcaveOn 𝕜 s f) (g : E ->ₗ[𝕜] F)
  证明: hf.dual.comp_linearMap g

Depends on / 依赖: comp_linearMap, hf.dual.comp_linearMap
-/
theorem ConcaveOn.comp_linearMap {f : F -> β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E ->ₗ[𝕜] F) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_linearMap g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]

section DistribMulAction

variable [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E -> β}

/--
theorem `StrictConvexOn.add_convexOn` / 定理 `StrictConvexOn.add_convexOn`

English:
theorem StrictConvexOn.add_convexOn
  given: (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

中文:
定理 StrictConvexOn.add_convexOn
  条件: (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

Depends on / 依赖: add_add_add_comm, add_lt_add_of_lt_of_le, ha.le, hb.le, smul_add
-/
theorem StrictConvexOn.add_convexOn (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

/--
theorem `ConvexOn.add_strictConvexOn` / 定理 `ConvexOn.add_strictConvexOn`

English:
theorem ConvexOn.add_strictConvexOn
  given: (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  proof: add_comm g f ▸ hg.add_convexOn hf

中文:
定理 ConvexOn.add_strictConvexOn
  条件: (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  证明: add_comm g f ▸ hg.add_convexOn hf

Depends on / 依赖: add_comm, add_convexOn, hg.add_convexOn
-/
theorem ConvexOn.add_strictConvexOn (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  add_comm g f ▸ hg.add_convexOn hf

/--
theorem `StrictConvexOn.add` / 定理 `StrictConvexOn.add`

English:
theorem StrictConvexOn.add
  given: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  proof: ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

中文:
定理 StrictConvexOn.add
  条件: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  证明: ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

Depends on / 依赖: add_add_add_comm, add_lt_add, smul_add
-/
theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

/--
theorem `StrictConcaveOn.add_concaveOn` / 定理 `StrictConcaveOn.add_concaveOn`

English:
theorem StrictConcaveOn.add_concaveOn
  given: (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: hf.dual.add_convexOn hg.dual

中文:
定理 StrictConcaveOn.add_concaveOn
  条件: (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: hf.dual.add_convexOn hg.dual

Depends on / 依赖: add_convexOn, hT.isSymmetric.isSelfAdjoint, hf.dual.add_convexOn, hg.dual, isSelfAdjoint, isSymmetric
-/
theorem StrictConcaveOn.add_concaveOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_convexOn hg.dual

/--
theorem `ConcaveOn.add_strictConcaveOn` / 定理 `ConcaveOn.add_strictConcaveOn`

English:
theorem ConcaveOn.add_strictConcaveOn
  given: (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  proof: hf.dual.add_strictConvexOn hg.dual

中文:
定理 ConcaveOn.add_strictConcaveOn
  条件: (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  证明: hf.dual.add_strictConvexOn hg.dual

Depends on / 依赖: add_strictConvexOn, hf.dual.add_strictConvexOn, hg.dual
-/
theorem ConcaveOn.add_strictConcaveOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_strictConvexOn hg.dual

/--
theorem `StrictConcaveOn.add` / 定理 `StrictConcaveOn.add`

English:
theorem StrictConcaveOn.add
  given: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  proof: hf.dual.add hg

中文:
定理 StrictConcaveOn.add
  条件: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  证明: hf.dual.add hg

Depends on / 依赖: hf.dual.add
-/
theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

/--
theorem `StrictConvexOn.add_const` / 定理 `StrictConvexOn.add_const`

English:
theorem StrictConvexOn.add_const
  statement: {γ : Type*} {f : E -> γ}
  proof: hf.add_convexOn (convexOn_const _ hf.1)

中文:
定理 StrictConvexOn.add_const
  结论: {γ : 类型} {f : E -> γ}
  证明: hf.add_convexOn (convexOn_const _ hf.1)

Depends on / 依赖: add_convexOn, convexOn_const, hf.add_convexOn
-/
theorem StrictConvexOn.add_const {γ : Type*} {f : E -> γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConvexOn 𝕜 s f) (b : γ) : StrictConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add_convexOn (convexOn_const _ hf.1)

/--
theorem `StrictConcaveOn.add_const` / 定理 `StrictConcaveOn.add_const`

English:
theorem StrictConcaveOn.add_const
  statement: {γ : Type*} {f : E -> γ}
  proof: hf.add_concaveOn (concaveOn_const _ hf.1)

中文:
定理 StrictConcaveOn.add_const
  结论: {γ : 类型} {f : E -> γ}
  证明: hf.add_concaveOn (concaveOn_const _ hf.1)

Depends on / 依赖: add_concaveOn, concaveOn_const, hf.add_concaveOn
-/
theorem StrictConcaveOn.add_const {γ : Type*} {f : E -> γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConcaveOn 𝕜 s f) (b : γ) : StrictConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add_concaveOn (concaveOn_const _ hf.1)

end DistribMulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `ConvexOn.convex_lt` / 定理 `ConvexOn.convex_lt`

English:
theorem ConvexOn.convex_lt
  given: (hf : ConvexOn 𝕜 s f) (r : β)
  statement: Convex 𝕜 ({ x in s | f x < r })
  proof: convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩

中文:
定理 ConvexOn.convex_lt
  条件: (hf : ConvexOn 𝕜 s f) (r : β)
  结论: 凸 𝕜 ({ x in s | f x < r })
  证明: convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩

Depends on / 依赖: Convex, Convex.combo_self, add_lt_add_of_lt_of_le, combo_self, convex_iff_forall_pos, hT.toLinearMap.re_inner_nonneg_right, ha.le, hb.le, re_inner_nonneg_right, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left, toLinearMap
-/
theorem ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | f x < r }) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) <= a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩

/--
theorem `ConcaveOn.convex_gt` / 定理 `ConcaveOn.convex_gt`

English:
theorem ConcaveOn.convex_gt
  given: (hf : ConcaveOn 𝕜 s f) (r : β)
  statement: Convex 𝕜 ({ x in s | r < f x })
  proof: hf.dual.convex_lt r

中文:
定理 ConcaveOn.convex_gt
  条件: (hf : ConcaveOn 𝕜 s f) (r : β)
  结论: 凸 𝕜 ({ x in s | r < f x })
  证明: hf.dual.convex_lt r

Depends on / 依赖: convex_lt, hf.dual.convex_lt
-/
theorem ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | r < f x }) :=
  hf.dual.convex_lt r

/--
theorem `ConvexOn.openSegment_subset_strict_epigraph` / 定理 `ConvexOn.openSegment_subset_strict_epigraph`

English:
theorem ConvexOn.openSegment_subset_strict_epigraph
  statement: (hf : ConvexOn 𝕜 s f) (p q : E × β)
  proof: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) <= a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)

中文:
定理 ConvexOn.openSegment_subset_strict_epigraph
  结论: (hf : ConvexOn 𝕜 s f) (p q : E × β)
  证明: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) <= a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)

Depends on / 依赖: add_lt_add_of_lt_of_le, ha.le, hb.le, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left
-/
theorem ConvexOn.openSegment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β)
    (hp : p.1 in s ∧ f p.1 < p.2) (hq : q.1 in s ∧ f q.1 <= q.2) :
    openSegment 𝕜 p q subseteq { p : E × β | p.1 in s ∧ f p.1 < p.2 } := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) <= a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)

/--
theorem `ConcaveOn.openSegment_subset_strict_hypograph` / 定理 `ConcaveOn.openSegment_subset_strict_hypograph`

English:
theorem ConcaveOn.openSegment_subset_strict_hypograph
  statement: (hf : ConcaveOn 𝕜 s f) (p q : E × β)
  proof: hf.dual.openSegment_subset_strict_epigraph p q hp hq

中文:
定理 ConcaveOn.openSegment_subset_strict_hypograph
  结论: (hf : ConcaveOn 𝕜 s f) (p q : E × β)
  证明: hf.dual.openSegment_subset_strict_epigraph p q hp hq

Depends on / 依赖: hT.toLinearMap.inner_nonneg_left, hf.dual.openSegment_subset_strict_epigraph, inner_nonneg_left, openSegment_subset_strict_epigraph, toLinearMap
-/
theorem ConcaveOn.openSegment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q : E × β)
    (hp : p.1 in s ∧ p.2 < f p.1) (hq : q.1 in s ∧ q.2 <= f q.1) :
    openSegment 𝕜 p q subseteq { p : E × β | p.1 in s ∧ p.2 < f p.1 } :=
  hf.dual.openSegment_subset_strict_epigraph p q hp hq

/--
theorem `ConvexOn.convex_strict_epigraph` / 定理 `ConvexOn.convex_strict_epigraph`

English:
theorem ConvexOn.convex_strict_epigraph
  given: [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f)
  proof: convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

中文:
定理 ConvexOn.convex_strict_epigraph
  条件: [ZeroLEOne类 𝕜] (hf : ConvexOn 𝕜 s f)
  证明: convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

Depends on / 依赖: convex_iff_openSegment_subset, convex_iff_openSegment_subset.mpr, hT.toLinearMap.inner_nonneg_right, hf.openSegment_subset_strict_epigraph, inner_nonneg_right, openSegment_subset_strict_epigraph, toLinearMap
-/
theorem ConvexOn.convex_strict_epigraph [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 < p.2 } :=
  convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

/--
theorem `ConcaveOn.convex_strict_hypograph` / 定理 `ConcaveOn.convex_strict_hypograph`

English:
theorem ConcaveOn.convex_strict_hypograph
  given: [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f)
  proof: hf.dual.convex_strict_epigraph

中文:
定理 ConcaveOn.convex_strict_hypograph
  条件: [ZeroLEOne类 𝕜] (hf : ConcaveOn 𝕜 s f)
  证明: hf.dual.convex_strict_epigraph

Depends on / 依赖: convex_strict_epigraph, hf.dual.convex_strict_epigraph
-/
theorem ConcaveOn.convex_strict_hypograph [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E}
  {f g : E -> β}

/--
theorem `ConvexOn.sup` / 定理 `ConvexOn.sup`

English:
theorem ConvexOn.sup
  given: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  statement: ConvexOn 𝕜 s (f ⊔ g)
  proof: by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) <= a • f x + b • f y := hf.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) <= a • g x + b • g y := hg.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

中文:
定理 ConvexOn.上确界
  条件: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  结论: ConvexOn 𝕜 s (f ⊔ g)
  证明: by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) <= a • f x + b • f y := hf.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) <= a • g x + b • g y := hg.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

Depends on / 依赖: hf.left, hf.right, hg.right, le_sup_left, le_sup_right, sup_le
-/
theorem ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f ⊔ g) := by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) <= a • f x + b • f y := hf.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) <= a • g x + b • g y := hg.right hx hy ha hb hab
      _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

/--
theorem `ConcaveOn.inf` / 定理 `ConcaveOn.inf`

English:
theorem ConcaveOn.inf
  given: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  statement: ConcaveOn 𝕜 s (f ⊓ g)
  proof: hf.dual.sup hg

中文:
定理 ConcaveOn.下确界
  条件: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  结论: ConcaveOn 𝕜 s (f ⊓ g)
  证明: hf.dual.sup hg

Depends on / 依赖: hf.dual.sup
-/
theorem ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/--
theorem `StrictConvexOn.sup` / 定理 `StrictConvexOn.sup`

English:
theorem StrictConvexOn.sup
  given: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  proof: ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

中文:
定理 StrictConvexOn.上确界
  条件: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  证明: ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

Depends on / 依赖: hf.left, le_sup_left, le_sup_right, max_lt
-/
theorem StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f ⊔ g) :=
  ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ <= a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

/--
theorem `StrictConcaveOn.inf` / 定理 `StrictConcaveOn.inf`

English:
theorem StrictConcaveOn.inf
  given: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  proof: hf.dual.sup hg

中文:
定理 StrictConcaveOn.下确界
  条件: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  证明: hf.dual.sup hg

Depends on / 依赖: hf.dual.sup
-/
theorem StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/--
theorem `ConvexOn.le_on_segment'` / 定理 `ConvexOn.le_on_segment'`

English:
theorem ConvexOn.le_on_segment'
  statement: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜}
  proof: calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

中文:
定理 ConvexOn.le_on_segment'
  结论: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜}
  证明: calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, combo_self, hS.toLinearMap, hT.toLinearMap.add, isPositive_toLinearMap_iff, le_max_left, le_max_right, toLinearMap
-/
theorem ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜}
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) : f (a • x + b • y) <= max (f x) (f y) :=
  calc
    f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/--
theorem `ConcaveOn.ge_on_segment'` / 定理 `ConcaveOn.ge_on_segment'`

English:
theorem ConcaveOn.ge_on_segment'
  statement: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.le_on_segment' hx hy ha hb hab

中文:
定理 ConcaveOn.ge_on_segment'
  结论: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.le_on_segment' hx hy ha hb hab

Depends on / 依赖: hf.dual.le_on_segment, le_on_segment
-/
theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
    {a b : 𝕜} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) : min (f x) (f y) <= f (a • x + b • y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

/--
theorem `ConvexOn.le_on_segment` / 定理 `ConvexOn.le_on_segment`

English:
theorem ConvexOn.le_on_segment
  statement: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

中文:
定理 ConvexOn.le_on_segment
  结论: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

Depends on / 依赖: hT.toLinearMap.smul_of_nonneg, hf.le_on_segment, isPositive_toLinearMap_iff, le_on_segment, smul_of_nonneg, toLinearMap
-/
theorem ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in [x -[𝕜] y]) : f z <= max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

/--
theorem `ConcaveOn.ge_on_segment` / 定理 `ConcaveOn.ge_on_segment`

English:
theorem ConcaveOn.ge_on_segment
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.le_on_segment hx hy hz

中文:
定理 ConcaveOn.ge_on_segment
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.le_on_segment hx hy hz

Depends on / 依赖: hf.dual.le_on_segment, le_on_segment
-/
theorem ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in [x -[𝕜] y]) : min (f x) (f y) <= f z :=
  hf.dual.le_on_segment hx hy hz

/--
theorem `StrictConvexOn.lt_on_open_segment'` / 定理 `StrictConvexOn.lt_on_open_segment'`

English:
theorem StrictConvexOn.lt_on_open_segment'
  statement: (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x in s)
  proof: calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

中文:
定理 StrictConvexOn.lt_on_open_segment'
  结论: (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x in s)
  证明: calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, combo_self, le_max_left, le_max_right
-/
theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x in s)
    (hy : y in s) (hxy : x != y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    f (a • x + b • y) < max (f x) (f y) :=
  calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ <= a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/--
theorem `StrictConcaveOn.lt_on_open_segment'` / 定理 `StrictConcaveOn.lt_on_open_segment'`

English:
theorem StrictConcaveOn.lt_on_open_segment'
  statement: (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x in s)
  proof: hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

中文:
定理 StrictConcaveOn.lt_on_open_segment'
  结论: (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x in s)
  证明: hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

Depends on / 依赖: hf.dual.lt_on_open_segment, lt_on_open_segment
-/
theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x in s)
    (hy : y in s) (hxy : x != y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min (f x) (f y) < f (a • x + b • y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/--
theorem `StrictConvexOn.lt_on_openSegment` / 定理 `StrictConvexOn.lt_on_openSegment`

English:
theorem StrictConvexOn.lt_on_openSegment
  statement: (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x in s)
  proof: let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

中文:
定理 StrictConvexOn.lt_on_openSegment
  结论: (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x in s)
  证明: let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

Depends on / 依赖: hf.lt_on_open_segment, lt_on_open_segment
-/
theorem StrictConvexOn.lt_on_openSegment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x in s)
    (hy : y in s) (hxy : x != y) (hz : z in openSegment 𝕜 x y) : f z < max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/--
theorem `StrictConcaveOn.lt_on_openSegment` / 定理 `StrictConcaveOn.lt_on_openSegment`

English:
theorem StrictConcaveOn.lt_on_openSegment
  statement: (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x in s)
  proof: hf.dual.lt_on_openSegment hx hy hxy hz

中文:
定理 StrictConcaveOn.lt_on_openSegment
  结论: (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x in s)
  证明: hf.dual.lt_on_openSegment hx hy hxy hz

Depends on / 依赖: hf.dual.lt_on_openSegment, lt_on_openSegment
-/
theorem StrictConcaveOn.lt_on_openSegment (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x in s)
    (hy : y in s) (hxy : x != y) (hz : z in openSegment 𝕜 x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_openSegment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

section PosSMulStrictMono

variable [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E -> β}

/--
theorem `ConvexOn.le_left_of_right_le'` / 定理 `ConvexOn.le_left_of_right_le'`

English:
theorem ConvexOn.le_left_of_right_le'
  statement: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  proof: le_of_not_gt fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

中文:
定理 ConvexOn.le_left_of_right_le'
  结论: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  证明: le_of_not_gt fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, add_lt_add_of_lt_of_le, combo_self, ha.le, le_of_not_gt, lt_irrefl, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left
-/
theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) (hfy : f y <= f (a • x + b • y)) :
    f (a • x + b • y) <= f x :=
le_of_not_gt fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

/--
theorem `ConcaveOn.left_le_of_le_right'` / 定理 `ConcaveOn.left_le_of_le_right'`

English:
theorem ConcaveOn.left_le_of_le_right'
  statement: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

中文:
定理 ConcaveOn.left_le_of_le_right'
  结论: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

Depends on / 依赖: hf.dual.le_left_of_right_le, le_left_of_right_le
-/
theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) (hfy : f (a • x + b • y) <= f y) :
    f x <= f (a • x + b • y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

/--
theorem `ConvexOn.le_right_of_left_le'` / 定理 `ConvexOn.le_right_of_left_le'`

English:
theorem ConvexOn.le_right_of_left_le'
  statement: (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  proof: by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

中文:
定理 ConvexOn.le_right_of_left_le'
  结论: (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  证明: by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

Depends on / 依赖: add_comm, hf.le_left_of_right_le, le_left_of_right_le
-/
theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
    (hy : y in s) (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x <= f (a • x + b • y)) :
    f (a • x + b • y) <= f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

/--
theorem `ConcaveOn.right_le_of_le_left'` / 定理 `ConcaveOn.right_le_of_le_left'`

English:
theorem ConcaveOn.right_le_of_le_left'
  statement: (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  proof: hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

中文:
定理 ConcaveOn.right_le_of_le_left'
  结论: (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  证明: hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

Depends on / 依赖: hf.dual.le_right_of_left_le, le_right_of_left_le
-/
theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
    (hy : y in s) (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) <= f x) :
    f y <= f (a • x + b • y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

/--
theorem `ConvexOn.le_left_of_right_le` / 定理 `ConvexOn.le_left_of_right_le`

English:
theorem ConvexOn.le_left_of_right_le
  statement: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

中文:
定理 ConvexOn.le_left_of_right_le
  结论: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

Depends on / 依赖: hb.le, hf.le_left_of_right_le, le_left_of_right_le
-/
theorem ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hyz : f y <= f z) : f z <= f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

/--
theorem `ConcaveOn.left_le_of_le_right` / 定理 `ConcaveOn.left_le_of_le_right`

English:
theorem ConcaveOn.left_le_of_le_right
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.le_left_of_right_le hx hy hz hyz

中文:
定理 ConcaveOn.left_le_of_le_right
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.le_left_of_right_le hx hy hz hyz

Depends on / 依赖: hf.dual.le_left_of_right_le, le_left_of_right_le
-/
theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hyz : f z <= f y) : f x <= f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz

/--
theorem `ConvexOn.le_right_of_left_le` / 定理 `ConvexOn.le_right_of_left_le`

English:
theorem ConvexOn.le_right_of_left_le
  statement: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

中文:
定理 ConvexOn.le_right_of_left_le
  结论: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

Depends on / 依赖: ha.le, hf.le_right_of_left_le, le_right_of_left_le
-/
theorem ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hxz : f x <= f z) : f z <= f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

/--
theorem `ConcaveOn.right_le_of_le_left` / 定理 `ConcaveOn.right_le_of_le_left`

English:
theorem ConcaveOn.right_le_of_le_left
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.le_right_of_left_le hx hy hz hxz

中文:
定理 ConcaveOn.right_le_of_le_left
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.le_right_of_left_le hx hy hz hxz

Depends on / 依赖: hf.dual.le_right_of_left_le, le_right_of_left_le
-/
theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hxz : f z <= f x) : f y <= f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end PosSMulStrictMono

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E -> β}


/--
theorem `ConvexOn.lt_left_of_right_lt'` / 定理 `ConvexOn.lt_left_of_right_lt'`

English:
theorem ConvexOn.lt_left_of_right_lt'
  statement: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  proof: not_le.1 fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

中文:
定理 ConvexOn.lt_left_of_right_lt'
  结论: (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  证明: not_le.1 fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, add_lt_add_of_le_of_lt, combo_self, ha.le, hb.le, lt_irrefl, not_le, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left
-/
theorem ConvexOn.lt_left_of_right_lt' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a • x + b • y)) :
    f (a • x + b • y) < f x :=
not_le.1 fun h => lt_irrefl (f (a • x + b • y))
    calc
      f (a • x + b • y) <= a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

/--
theorem `ConcaveOn.left_lt_of_lt_right'` / 定理 `ConcaveOn.left_lt_of_lt_right'`

English:
theorem ConcaveOn.left_lt_of_lt_right'
  statement: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

中文:
定理 ConcaveOn.left_lt_of_lt_right'
  结论: (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

Depends on / 依赖: hf.dual.lt_left_of_right_lt, lt_left_of_right_lt
-/
theorem ConcaveOn.left_lt_of_lt_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a • x + b • y) < f y) :
    f x < f (a • x + b • y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

/--
theorem `ConvexOn.lt_right_of_left_lt'` / 定理 `ConvexOn.lt_right_of_left_lt'`

English:
theorem ConvexOn.lt_right_of_left_lt'
  statement: (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  proof: by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

中文:
定理 ConvexOn.lt_right_of_left_lt'
  结论: (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  证明: by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

Depends on / 依赖: add_comm, hf.lt_left_of_right_lt, lt_left_of_right_lt
-/
theorem ConvexOn.lt_right_of_left_lt' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
    (hy : y in s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a • x + b • y)) :
    f (a • x + b • y) < f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

/--
theorem `ConcaveOn.lt_right_of_left_lt'` / 定理 `ConcaveOn.lt_right_of_left_lt'`

English:
theorem ConcaveOn.lt_right_of_left_lt'
  statement: (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  proof: hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

中文:
定理 ConcaveOn.lt_right_of_left_lt'
  结论: (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
  证明: hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

Depends on / 依赖: hf.dual.lt_right_of_left_lt, lt_right_of_left_lt
-/
theorem ConcaveOn.lt_right_of_left_lt' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s)
    (hy : y in s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) < f x) :
    f y < f (a • x + b • y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

/--
theorem `ConvexOn.lt_left_of_right_lt` / 定理 `ConvexOn.lt_left_of_right_lt`

English:
theorem ConvexOn.lt_left_of_right_lt
  statement: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

中文:
定理 ConvexOn.lt_left_of_right_lt
  结论: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

Depends on / 依赖: hf.lt_left_of_right_lt, lt_left_of_right_lt
-/
theorem ConvexOn.lt_left_of_right_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hyz : f y < f z) : f z < f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

/--
theorem `ConcaveOn.left_lt_of_lt_right` / 定理 `ConcaveOn.left_lt_of_lt_right`

English:
theorem ConcaveOn.left_lt_of_lt_right
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.lt_left_of_right_lt hx hy hz hyz

中文:
定理 ConcaveOn.left_lt_of_lt_right
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.lt_left_of_right_lt hx hy hz hyz

Depends on / 依赖: hf.dual.lt_left_of_right_lt, lt_left_of_right_lt
-/
theorem ConcaveOn.left_lt_of_lt_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz

/--
theorem `ConvexOn.lt_right_of_left_lt` / 定理 `ConvexOn.lt_right_of_left_lt`

English:
theorem ConvexOn.lt_right_of_left_lt
  statement: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

中文:
定理 ConvexOn.lt_right_of_left_lt
  结论: (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

Depends on / 依赖: hf.lt_right_of_left_lt, lt_right_of_left_lt
-/
theorem ConvexOn.lt_right_of_left_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hxz : f x < f z) : f z < f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

/--
theorem `ConcaveOn.lt_right_of_left_lt` / 定理 `ConcaveOn.lt_right_of_left_lt`

English:
theorem ConcaveOn.lt_right_of_left_lt
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  proof: hf.dual.lt_right_of_left_lt hx hy hz hxz

中文:
定理 ConcaveOn.lt_right_of_left_lt
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
  证明: hf.dual.lt_right_of_left_lt hx hy hz hxz

Depends on / 依赖: hf.dual.lt_right_of_left_lt, lt_right_of_left_lt
-/
theorem ConcaveOn.lt_right_of_left_lt (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s)
    (hz : z in openSegment 𝕜 x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
  {s : Set E} {f g : E -> β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp]
/--
theorem `neg_convexOn_iff` / 定理 `neg_convexOn_iff`

English:
theorem neg_convexOn_iff
  statement: ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
  proof: by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simpa [add_comm] using h hx hy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy ha hb hab

中文:
定理 neg_convexOn_iff
  结论: ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
  证明: by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simpa [add_comm] using h hx hy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy ha hb hab

Depends on / 依赖: Pi.neg_apply, add_comm, neg_add, neg_apply, neg_le_neg_iff, neg_neg, simp_rw, smul_neg
-/
theorem neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simpa [add_comm] using h hx hy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy ha hb hab

/-- A function `-f` is concave iff `f` is convex. -/
@[simp]
/--
theorem `neg_concaveOn_iff` / 定理 `neg_concaveOn_iff`

English:
theorem neg_concaveOn_iff
  statement: ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f
  proof: by
  rw [← neg_convexOn_iff]; rw [neg_neg f]

中文:
定理 neg_concaveOn_iff
  结论: ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f
  证明: by
  rw [← neg_convexOn_iff]; rw [neg_neg f]

Depends on / 依赖: neg_convexOn_iff, neg_neg
-/
theorem neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f := by
  rw [← neg_convexOn_iff]; rw [neg_neg f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp]
/--
theorem `neg_strictConvexOn_iff` / 定理 `neg_strictConvexOn_iff`

English:
theorem neg_strictConvexOn_iff
  statement: StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f
  proof: by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    simp only [ne_eq, Pi.neg_apply, smul_neg, lt_add_neg_iff_add_lt, add_comm,
      add_neg_lt_iff_lt_add] at h
    exact h hx hy hxy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy hxy ha hb hab

中文:
定理 neg_strictConvexOn_iff
  结论: StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f
  证明: by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    simp only [ne_eq, Pi.neg_apply, smul_neg, lt_add_neg_iff_add_lt, add_comm,
      add_neg_lt_iff_lt_add] at h
    exact h hx hy hxy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy hxy ha hb hab

Depends on / 依赖: Pi.neg_apply, add_comm, add_neg_lt_iff_lt_add, lt_add_neg_iff_add_lt, ne_eq, neg_add, neg_apply, neg_lt_neg_iff, neg_neg, simp_rw, smul_neg
-/
theorem neg_strictConvexOn_iff : StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    simp only [ne_eq, Pi.neg_apply, smul_neg, lt_add_neg_iff_add_lt, add_comm,
      add_neg_lt_iff_lt_add] at h
    exact h hx hy hxy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy hxy ha hb hab

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp]
/--
theorem `neg_strictConcaveOn_iff` / 定理 `neg_strictConcaveOn_iff`

English:
theorem neg_strictConcaveOn_iff
  statement: StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f
  proof: by
  rw [← neg_strictConvexOn_iff]; rw [neg_neg f]

alias ⟨_, ConcaveOn.neg⟩ := neg_convexOn_iff

alias ⟨_, ConvexOn.neg⟩ := neg_concaveOn_iff

alias ⟨_, StrictConcaveOn.neg⟩ := neg_strictConvexOn_iff

alias ⟨_, StrictConvexOn.neg⟩ := neg_strictConcaveOn_iff

中文:
定理 neg_strictConcaveOn_iff
  结论: StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f
  证明: by
  rw [← neg_strictConvexOn_iff]; rw [neg_neg f]

alias ⟨_, ConcaveOn.neg⟩ := neg_convexOn_iff

alias ⟨_, ConvexOn.neg⟩ := neg_concaveOn_iff

alias ⟨_, StrictConcaveOn.neg⟩ := neg_strictConvexOn_iff

alias ⟨_, StrictConvexOn.neg⟩ := neg_strictConcaveOn_iff

Depends on / 依赖: neg_neg, neg_strictConvexOn_iff
-/
theorem neg_strictConcaveOn_iff : StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff]; rw [neg_neg f]

alias ⟨_, ConcaveOn.neg⟩ := neg_convexOn_iff

alias ⟨_, ConvexOn.neg⟩ := neg_concaveOn_iff

alias ⟨_, StrictConcaveOn.neg⟩ := neg_strictConvexOn_iff

alias ⟨_, StrictConvexOn.neg⟩ := neg_strictConcaveOn_iff

/--
theorem `ConvexOn.sub` / 定理 `ConvexOn.sub`

English:
theorem ConvexOn.sub
  given: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  statement: ConvexOn 𝕜 s (f - g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

中文:
定理 ConvexOn.sub
  条件: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  结论: ConvexOn 𝕜 s (f - g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

/--
theorem `ConcaveOn.sub` / 定理 `ConcaveOn.sub`

English:
theorem ConcaveOn.sub
  given: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  statement: ConcaveOn 𝕜 s (f - g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

中文:
定理 ConcaveOn.sub
  条件: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  结论: ConcaveOn 𝕜 s (f - g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

/--
theorem `StrictConvexOn.sub` / 定理 `StrictConvexOn.sub`

English:
theorem StrictConvexOn.sub
  given: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

中文:
定理 StrictConvexOn.sub
  条件: (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

/--
theorem `StrictConcaveOn.sub` / 定理 `StrictConcaveOn.sub`

English:
theorem StrictConcaveOn.sub
  given: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

中文:
定理 StrictConcaveOn.sub
  条件: (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

/--
theorem `ConvexOn.sub_strictConcaveOn` / 定理 `ConvexOn.sub_strictConcaveOn`

English:
theorem ConvexOn.sub_strictConcaveOn
  given: (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add_strictConvexOn hg.neg

中文:
定理 ConvexOn.sub_strictConcaveOn
  条件: (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add_strictConvexOn hg.neg

Depends on / 依赖: add_strictConvexOn, hf.add_strictConvexOn, hg.neg, sub_eq_add_neg
-/
theorem ConvexOn.sub_strictConcaveOn (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConvexOn hg.neg

/--
theorem `ConcaveOn.sub_strictConvexOn` / 定理 `ConcaveOn.sub_strictConvexOn`

English:
theorem ConcaveOn.sub_strictConvexOn
  given: (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add_strictConcaveOn hg.neg

中文:
定理 ConcaveOn.sub_strictConvexOn
  条件: (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add_strictConcaveOn hg.neg

Depends on / 依赖: add_strictConcaveOn, hf.add_strictConcaveOn, hg.neg, sub_eq_add_neg
-/
theorem ConcaveOn.sub_strictConvexOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConcaveOn hg.neg

/--
theorem `StrictConvexOn.sub_concaveOn` / 定理 `StrictConvexOn.sub_concaveOn`

English:
theorem StrictConvexOn.sub_concaveOn
  given: (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add_convexOn hg.neg

中文:
定理 StrictConvexOn.sub_concaveOn
  条件: (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add_convexOn hg.neg

Depends on / 依赖: add_convexOn, hf.add_convexOn, hg.neg, sub_eq_add_neg
-/
theorem StrictConvexOn.sub_concaveOn (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_convexOn hg.neg

/--
theorem `StrictConcaveOn.sub_convexOn` / 定理 `StrictConcaveOn.sub_convexOn`

English:
theorem StrictConcaveOn.sub_convexOn
  given: (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add_concaveOn hg.neg

中文:
定理 StrictConcaveOn.sub_convexOn
  条件: (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add_concaveOn hg.neg

Depends on / 依赖: add_concaveOn, hf.add_concaveOn, hg.neg, sub_eq_add_neg
-/
theorem StrictConcaveOn.sub_convexOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_concaveOn hg.neg

end OrderedAddCommGroup

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [SMul 𝕜 β]
  {s : Set E}
  {f : E -> β}

/--
theorem `StrictConvexOn.translate_right` / 定理 `StrictConvexOn.translate_right`

English:
theorem StrictConvexOn.translate_right
  given: (hf : StrictConvexOn 𝕜 s f) (c : E)
  proof: ⟨hf.1.translate_preimage_right _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

中文:
定理 StrictConvexOn.translate_right
  条件: (hf : StrictConvexOn 𝕜 s f) (c : E)
  证明: ⟨hf.1.translate_preimage_right _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

Depends on / 依赖: Convex, Convex.combo_self, add_add_add_comm, add_right_injective, combo_self, smul_add, translate_preimage_right
-/
theorem StrictConvexOn.translate_right (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]; rw [Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

/--
theorem `StrictConcaveOn.translate_right` / 定理 `StrictConcaveOn.translate_right`

English:
theorem StrictConcaveOn.translate_right
  given: (hf : StrictConcaveOn 𝕜 s f) (c : E)
  proof: hf.dual.translate_right _

中文:
定理 StrictConcaveOn.translate_right
  条件: (hf : StrictConcaveOn 𝕜 s f) (c : E)
  证明: hf.dual.translate_right _

Depends on / 依赖: hf.dual.translate_right, translate_right
-/
theorem StrictConcaveOn.translate_right (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/--
theorem `StrictConvexOn.translate_left` / 定理 `StrictConvexOn.translate_left`

English:
theorem StrictConvexOn.translate_left
  given: (hf : StrictConvexOn 𝕜 s f) (c : E)
  proof: by
  simpa only [add_comm] using hf.translate_right c

中文:
定理 StrictConvexOn.translate_left
  条件: (hf : StrictConvexOn 𝕜 s f) (c : E)
  证明: by
  simpa only [add_comm] using hf.translate_right c

Depends on / 依赖: add_comm, hf.translate_right, translate_right
-/
theorem StrictConvexOn.translate_left (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

/--
theorem `StrictConcaveOn.translate_left` / 定理 `StrictConcaveOn.translate_left`

English:
theorem StrictConcaveOn.translate_left
  given: (hf : StrictConcaveOn 𝕜 s f) (c : E)
  proof: by
  simpa only [add_comm] using hf.translate_right c

中文:
定理 StrictConcaveOn.translate_left
  条件: (hf : StrictConcaveOn 𝕜 s f) (c : E)
  证明: by
  simpa only [add_comm] using hf.translate_right c

Depends on / 依赖: add_comm, hf.translate_right, translate_right
-/
theorem StrictConcaveOn.translate_left (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

end AddCancelCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β] {s : Set E} {f : E -> β}

/--
theorem `ConvexOn.smul` / 定理 `ConvexOn.smul`

English:
theorem ConvexOn.smul
  given: {c : 𝕜} (hc : 0 <= c) (hf : ConvexOn 𝕜 s f)
  statement: ConvexOn 𝕜 s fun x => c • f x
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) <= c • (a • f x + b • f y) :=
        smul_le_smul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

中文:
定理 ConvexOn.smul
  条件: {c : 𝕜} (hc : 0 <= c) (hf : ConvexOn 𝕜 s f)
  结论: ConvexOn 𝕜 s fun x => c • f x
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) <= c • (a • f x + b • f y) :=
        smul_le_smul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

Depends on / 依赖: smul_add, smul_comm, smul_le_smul_of_nonneg_left
-/
theorem ConvexOn.smul {c : 𝕜} (hc : 0 <= c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s fun x => c • f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) <= c • (a • f x + b • f y) :=
        smul_le_smul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

/--
theorem `ConcaveOn.smul` / 定理 `ConcaveOn.smul`

English:
theorem ConcaveOn.smul
  given: {c : 𝕜} (hc : 0 <= c) (hf : ConcaveOn 𝕜 s f)
  proof: hf.dual.smul hc

中文:
定理 ConcaveOn.smul
  条件: {c : 𝕜} (hc : 0 <= c) (hf : ConcaveOn 𝕜 s f)
  证明: hf.dual.smul hc

Depends on / 依赖: hf.dual.smul
-/
theorem ConcaveOn.smul {c : 𝕜} (hc : 0 <= c) (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s fun x => c • f x :=
  hf.dual.smul hc

end Module

end OrderedAddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [AddCommGroup F]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/--
theorem `ConvexOn.comp_affineMap` / 定理 `ConvexOn.comp_affineMap`

English:
theorem ConvexOn.comp_affineMap
  given: {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f)
  proof: ⟨hf.1.affine_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by rw [Convex.combo_affine_apply hab]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

中文:
定理 ConvexOn.comp_affineMap
  条件: {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : 集合 F} (hf : ConvexOn 𝕜 s f)
  证明: ⟨hf.1.affine_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by rw [Convex.combo_affine_apply hab]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

Depends on / 依赖: Convex, Convex.combo_affine_apply, affine_preimage, combo_affine_apply
-/
theorem ConvexOn.comp_affineMap {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.affine_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by rw [Convex.combo_affine_apply hab]
      _ <= a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/--
theorem `ConcaveOn.comp_affineMap` / 定理 `ConcaveOn.comp_affineMap`

English:
theorem ConcaveOn.comp_affineMap
  given: {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f)
  proof: hf.dual.comp_affineMap g

中文:
定理 ConcaveOn.comp_affineMap
  条件: {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : 集合 F} (hf : ConcaveOn 𝕜 s f)
  证明: hf.dual.comp_affineMap g

Depends on / 依赖: comp_affineMap, hf.dual.comp_affineMap
-/
theorem ConcaveOn.comp_affineMap {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_affineMap g

end Module

end OrderedAddCommMonoid

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section SMul

variable [SMul 𝕜 E] [SMul 𝕜 β] {s : Set E}

/--
theorem `convexOn_iff_div` / 定理 `convexOn_iff_div`

English:
theorem convexOn_iff_div
  given: {f : E -> β}
  proof: and_congr Iff.rfl ⟨by
    intro h x hx y hy a b ha hb hab
    apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy ha hb⟩

中文:
定理 convexOn_iff_div
  条件: {f : E -> β}
  证明: and_congr Iff.rfl ⟨by
    intro h x hx y hy a b ha hb hab
    apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy ha hb⟩

Depends on / 依赖: Iff.rfl, add_div, and_congr, div_nonneg, div_self, hab.le, hab.ne, zero_lt_one
-/
theorem convexOn_iff_div {f : E -> β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b ->
        f ((a / (a + b)) • x + (b / (a + b)) • y) <= (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy a b ha hb hab
    apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy ha hb⟩

/--
theorem `concaveOn_iff_div` / 定理 `concaveOn_iff_div`

English:
theorem concaveOn_iff_div
  given: {f : E -> β}
  proof: convexOn_iff_div (β := βᵒᵈ)

中文:
定理 concaveOn_iff_div
  条件: {f : E -> β}
  证明: convexOn_iff_div (β := βᵒᵈ)

Depends on / 依赖: convexOn_iff_div
-/
theorem concaveOn_iff_div {f : E -> β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b ->
        (a / (a + b)) • f x + (b / (a + b)) • f y <= f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  convexOn_iff_div (β := βᵒᵈ)

/--
theorem `strictConvexOn_iff_div` / 定理 `strictConvexOn_iff_div`

English:
theorem strictConvexOn_iff_div
  given: {f : E -> β}
  proof: and_congr Iff.rfl ⟨by
    intro h x hx y hy hxy a b ha hb
    have hab := add_pos ha hb
    apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy hxy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy hxy ha hb⟩

中文:
定理 strictConvexOn_iff_div
  条件: {f : E -> β}
  证明: and_congr Iff.rfl ⟨by
    intro h x hx y hy hxy a b ha hb
    have hab := add_pos ha hb
    apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy hxy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy hxy ha hb⟩

Depends on / 依赖: Iff.rfl, add_div, add_pos, and_congr, div_pos, div_self, hab.ne, zero_lt_one
-/
theorem strictConvexOn_iff_div {f : E -> β} :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b ->
        f ((a / (a + b)) • x + (b / (a + b)) • y) < (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy hxy a b ha hb
    have hab := add_pos ha hb
    apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
    rw [← add_div]; rw [div_self hab.ne'], by
    intro h x hx y hy hxy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy hxy ha hb⟩

/--
theorem `strictConcaveOn_iff_div` / 定理 `strictConcaveOn_iff_div`

English:
theorem strictConcaveOn_iff_div
  given: {f : E -> β}
  proof: strictConvexOn_iff_div (β := βᵒᵈ)

中文:
定理 strictConcaveOn_iff_div
  条件: {f : E -> β}
  证明: strictConvexOn_iff_div (β := βᵒᵈ)

Depends on / 依赖: strictConvexOn_iff_div
-/
theorem strictConcaveOn_iff_div {f : E -> β} :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b ->
        (a / (a + b)) • f x + (b / (a + b)) • f y < f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  strictConvexOn_iff_div (β := βᵒᵈ)

end SMul

end OrderedAddCommMonoid

end LinearOrderedField

section OrderIso

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid α] [PartialOrder α] [SMul 𝕜 α]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/--
theorem `OrderIso.strictConvexOn_symm` / 定理 `OrderIso.strictConvexOn_symm`

English:
theorem OrderIso.strictConvexOn_symm
  given: (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f)
  proof: by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

中文:
定理 OrderIso.strictConvexOn_symm
  条件: (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f)
  证明: by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, OrderIso.symm_apply_apply, apply_symm_apply, convex_univ, f.injective.ne_iff, f.lt_iff_lt, f.surjective.exists.mp, gt_iff_lt, injective, lt_iff_lt, ne_iff, surjective, symm_apply_apply
-/
theorem OrderIso.strictConvexOn_symm (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f) :
    StrictConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

/--
theorem `OrderIso.convexOn_symm` / 定理 `OrderIso.convexOn_symm`

English:
theorem OrderIso.convexOn_symm
  given: (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f)
  proof: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

中文:
定理 OrderIso.convexOn_symm
  条件: (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f)
  证明: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, OrderIso.symm_apply_apply, apply_symm_apply, convex_univ, f.le_iff_le, f.surjective.exists.mp, le_iff_le, surjective, symm_apply_apply
-/
theorem OrderIso.convexOn_symm (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f) :
    ConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

/--
theorem `OrderIso.strictConcaveOn_symm` / 定理 `OrderIso.strictConcaveOn_symm`

English:
theorem OrderIso.strictConcaveOn_symm
  given: (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f)
  proof: by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

中文:
定理 OrderIso.strictConcaveOn_symm
  条件: (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f)
  证明: by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, OrderIso.symm_apply_apply, apply_symm_apply, convex_univ, f.injective.ne_iff, f.lt_iff_lt, f.surjective.exists.mp, gt_iff_lt, injective, lt_iff_lt, ne_iff, surjective, symm_apply_apply
-/
theorem OrderIso.strictConcaveOn_symm (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f) :
    StrictConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' != y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) hxy' ha hb hab

/--
theorem `OrderIso.concaveOn_symm` / 定理 `OrderIso.concaveOn_symm`

English:
theorem OrderIso.concaveOn_symm
  given: (f : α ≃o β) (hf : ConvexOn 𝕜 univ f)
  proof: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

中文:
定理 OrderIso.concaveOn_symm
  条件: (f : α ≃o β) (hf : ConvexOn 𝕜 univ f)
  证明: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, OrderIso.symm_apply_apply, apply_symm_apply, convex_univ, f.le_iff_le, f.surjective.exists.mp, le_iff_le, surjective, symm_apply_apply
-/
theorem OrderIso.concaveOn_symm (f : α ≃o β) (hf : ConvexOn 𝕜 univ f) :
    ConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le]; rw [OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' in univ) (by simp : y' in univ) ha hb hab

end OrderIso


section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [AddCommMonoid E] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  {f : E -> β} {s : Set E} {x y : E}

/--
lemma `StrictConvexOn.eq_of_isMinOn` / 引理 `StrictConvexOn.eq_of_isMinOn`

English:
lemma StrictConvexOn.eq_of_isMinOn
  statement: (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
  proof: by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
have hz : z in s := hf.1 hx hy (by simp) (by simp) by norm_num
  refine lt_irrefl (f z) ?_
  calc
f z < _ := hf.2 hx hy hxy (by simp) (by simp) by norm_num
    _ <= (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := by gcongr; exacts [hfx hz, hfy hz]
    _ = f z := by rw [← _root_.add_smul]; norm_num

中文:
引理 StrictConvexOn.eq_of_isMinOn
  结论: (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
  证明: by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
have hz : z in s := hf.1 hx hy (by simp) (by simp) by norm_num
  refine lt_irrefl (f z) ?_
  calc
f z < _ := hf.2 hx hy hxy (by simp) (by simp) by norm_num
    _ <= (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := by gcongr; exacts [hfx hz, hfy hz]
    _ = f z := by rw [← _root_.add_smul]; norm_num

Depends on / 依赖: _root_, _root_.add_smul, add_smul, exacts, lt_irrefl
-/
lemma StrictConvexOn.eq_of_isMinOn (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
    (hfy : IsMinOn f s y) (hx : x in s) (hy : y in s) : x = y := by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
have hz : z in s := hf.1 hx hy (by simp) (by simp) by norm_num
  refine lt_irrefl (f z) ?_
  calc
f z < _ := hf.2 hx hy hxy (by simp) (by simp) by norm_num
    _ <= (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := by gcongr; exacts [hfx hz, hfy hz]
    _ = f z := by rw [← _root_.add_smul]; norm_num

/--
lemma `StrictConcaveOn.eq_of_isMaxOn` / 引理 `StrictConcaveOn.eq_of_isMaxOn`

English:
lemma StrictConcaveOn.eq_of_isMaxOn
  statement: (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
  proof: hf.dual.eq_of_isMinOn hfx hfy hx hy

中文:
引理 StrictConcaveOn.eq_of_isMaxOn
  结论: (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
  证明: hf.dual.eq_of_isMinOn hfx hfy hx hy

Depends on / 依赖: eq_of_isMinOn, hf.dual.eq_of_isMinOn
-/
lemma StrictConcaveOn.eq_of_isMaxOn (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
    (hfy : IsMaxOn f s y) (hx : x in s) (hy : y in s) : x = y :=
  hf.dual.eq_of_isMinOn hfx hfy hx hy

end OrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid
variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]
  {x y z : 𝕜} {s : Set 𝕜} {f : 𝕜 -> β}

/--
theorem `ConvexOn.le_right_of_left_le''` / 定理 `ConvexOn.le_right_of_left_le''`

English:
theorem ConvexOn.le_right_of_left_le''
  statement: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x < y)
  proof: hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

中文:
定理 ConvexOn.le_right_of_left_le''
  结论: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x < y)
  证明: hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

Depends on / 依赖: Ioo_subset_openSegment, congr_arg, eq_or_lt, hf.le_right_of_left_le, hyz.eq_or_lt.elim, le_right_of_left_le
-/
theorem ConvexOn.le_right_of_left_le'' (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x < y)
    (hyz : y <= z) (h : f x <= f y) : f y <= f z :=
  hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

/--
theorem `ConvexOn.le_left_of_right_le''` / 定理 `ConvexOn.le_left_of_right_le''`

English:
theorem ConvexOn.le_left_of_right_le''
  statement: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x <= y)
  proof: hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

中文:
定理 ConvexOn.le_left_of_right_le''
  结论: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x <= y)
  证明: hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

Depends on / 依赖: Ioo_subset_openSegment, congr_arg, eq_or_lt, hf.le_left_of_right_le, hxy.eq_or_lt.elim, le_left_of_right_le
-/
theorem ConvexOn.le_left_of_right_le'' (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x <= y)
    (hyz : y < z) (h : f z <= f y) : f y <= f x :=
  hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

/--
theorem `ConcaveOn.right_le_of_le_left''` / 定理 `ConcaveOn.right_le_of_le_left''`

English:
theorem ConcaveOn.right_le_of_le_left''
  statement: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
  proof: hf.dual.le_right_of_left_le'' hx hz hxy hyz h

中文:
定理 ConcaveOn.right_le_of_le_left''
  结论: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
  证明: hf.dual.le_right_of_left_le'' hx hz hxy hyz h

Depends on / 依赖: hf.dual.le_right_of_left_le, le_right_of_left_le
-/
theorem ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y <= z) (h : f y <= f x) : f z <= f y :=
  hf.dual.le_right_of_left_le'' hx hz hxy hyz h

/--
theorem `ConcaveOn.left_le_of_le_right''` / 定理 `ConcaveOn.left_le_of_le_right''`

English:
theorem ConcaveOn.left_le_of_le_right''
  statement: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
  proof: hf.dual.le_left_of_right_le'' hx hz hxy hyz h

中文:
定理 ConcaveOn.left_le_of_le_right''
  结论: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
  证明: hf.dual.le_left_of_right_le'' hx hz hxy hyz h

Depends on / 依赖: hf.dual.le_left_of_right_le, le_left_of_right_le
-/
theorem ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz : z in s)
    (hxy : x <= y) (hyz : y < z) (h : f y <= f z) : f x <= f y :=
  hf.dual.le_left_of_right_le'' hx hz hxy hyz h

end LinearOrderedCancelAddCommMonoid
end LinearOrderedField
