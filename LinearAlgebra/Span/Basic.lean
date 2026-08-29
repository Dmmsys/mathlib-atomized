/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.BourbakiWitt

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Algebra.Module.Torsion.Field

/-!
# The span of a set of vectors, as a submodule

* `Submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notation

* We introduce the notation `R ∙ v` for the span of a singleton, `Submodule.span R {v}`. This is
  `\span`, not the same as the scalar multiplication `•`/`\bub`.

-/

@[expose] public section

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open scoped Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R ->+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂]

variable {s t : Set M}

/--
lemma `_root_.AddSubmonoid.toNatSubmodule_closure` / 引理 `_root_.AddSubmonoid.toNatSubmodule_closure`

English:
lemma _root_.AddSubmonoid.toNatSubmodule_closure
  given: (s : Set M)
  proof: (Submodule.span_le.mpr AddSubmonoid.subset_closure).antisymm'
    ((Submodule.span Nat s).toAddSubmonoid.closure_le.mpr Submodule.subset_span)

中文:
引理 _root_.加法子幺半群.to自然数Submodule_closure
  条件: (s : 集合 M)
  证明: (Submodule.span_le.mpr AddSubmonoid.subset_closure).antisymm'
    ((Submodule.span Nat s).toAddSubmonoid.closure_le.mpr Submodule.subset_span)

Depends on / 依赖: AddSubmonoid, AddSubmonoid.subset_closure, Submodule, Submodule.span, Submodule.span_le.mpr, Submodule.subset_span, antisymm, closure_le, span_le, subset_closure, subset_span, toAddSubmonoid, toAddSubmonoid.closure_le.mpr
-/
lemma _root_.AddSubmonoid.toNatSubmodule_closure (s : Set M) :
    (AddSubmonoid.closure s).toNatSubmodule = .span Nat s :=
  (Submodule.span_le.mpr AddSubmonoid.subset_closure).antisymm'
    ((Submodule.span Nat s).toAddSubmonoid.closure_le.mpr Submodule.subset_span)

/-- A version of `Submodule.span_eq` for when the span is by a smaller ring. -/
@[simp]
/--
theorem `span_coe_eq_restrictScalars` / 定理 `span_coe_eq_restrictScalars`

English:
theorem span_coe_eq_restrictScalars
  given: [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  proof: span_eq (p.restrictScalars S)

include σ₁₂ in

中文:
定理 span_coe_eq_restrictScalars
  条件: [半环 S] [标量乘法 S R] [模 S M] [标量塔 S R M]
  证明: span_eq (p.restrictScalars S)

include σ₁₂ in

Depends on / 依赖: p.restrictScalars, restrictScalars, span_eq
-/
theorem span_coe_eq_restrictScalars [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    span S (p : Set M) = p.restrictScalars S :=
  span_eq (p.restrictScalars S)

include σ₁₂ in
/--
theorem `image_span_subset` / 定理 `image_span_subset`

English:
theorem image_span_subset
  given: (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂)
  proof: image_subset_iff.trans span_le (p := N.comap f)

include σ₁₂ in

中文:
定理 image_span_subset
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (s : 集合 M) (N : 子模 R₂ M₂)
  证明: image_subset_iff.trans span_le (p := N.comap f)

include σ₁₂ in

Depends on / 依赖: N.comap, image_subset_iff, image_subset_iff.trans, span_le
-/
theorem image_span_subset (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
f '' span R s subseteq N ↔ forall m in s, f m in N := image_subset_iff.trans span_le (p := N.comap f)

include σ₁₂ in
/--
theorem `image_span_subset_span` / 定理 `image_span_subset_span`

English:
theorem image_span_subset_span
  given: (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M)
  statement: f '' span R s subseteq span R₂ (f '' s)
  proof: (image_span_subset f s _).2 fun x hx => subset_span ⟨x, hx, rfl⟩

中文:
定理 image_span_subset_span
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (s : 集合 M)
  结论: f '' span R s subseteq span R₂ (f '' s)
  证明: (image_span_subset f s _).2 fun x hx => subset_span ⟨x, hx, rfl⟩

Depends on / 依赖: image_span_subset, subset_span
-/
theorem image_span_subset_span (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) : f '' span R s subseteq span R₂ (f '' s) :=
  (image_span_subset f s _).2 fun x hx => subset_span ⟨x, hx, rfl⟩

/--
theorem `map_span` / 定理 `map_span`

English:
theorem map_span
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M)
  proof: Eq.symm span_eq_of_le _ (Set.image_mono subset_span) (image_span_subset_span f s)

alias _root_.LinearMap.map_span := Submodule.map_span

中文:
定理 map_span
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : 集合 M)
  证明: Eq.symm span_eq_of_le _ (Set.image_mono subset_span) (image_span_subset_span f s)

alias _root_.LinearMap.map_span := Submodule.map_span

Depends on / 依赖: Eq.symm, Set.image_mono, image_mono, image_span_subset_span, span_eq_of_le, subset_span
-/
theorem map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) :
    (span R s).map f = span R₂ (f '' s) :=
Eq.symm span_eq_of_le _ (Set.image_mono subset_span) (image_span_subset_span f s)

alias _root_.LinearMap.map_span := Submodule.map_span

/--
theorem `map_span_le` / 定理 `map_span_le`

English:
theorem map_span_le
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂)
  proof: image_span_subset f s N

alias _root_.LinearMap.map_span_le := Submodule.map_span_le

中文:
定理 map_span_le
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : 集合 M) (N : 子模 R₂ M₂)
  证明: image_span_subset f s N

alias _root_.LinearMap.map_span_le := Submodule.map_span_le

Depends on / 依赖: image_span_subset
-/
theorem map_span_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
    map f (span R s) <= N ↔ forall m in s, f m in N := image_span_subset f s N

alias _root_.LinearMap.map_span_le := Submodule.map_span_le

/--
theorem `span_preimage_le` / 定理 `span_preimage_le`

English:
theorem span_preimage_le
  given: (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M₂)
  proof: by
  rw [span_le]; rw [comap_coe]
  exact preimage_mono subset_span

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le

include σ₁₂ in

中文:
定理 span_preimage_le
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (s : 集合 M₂)
  证明: by
  rw [span_le]; rw [comap_coe]
  exact preimage_mono subset_span

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le

include σ₁₂ in

Depends on / 依赖: comap_coe, preimage_mono, span_le, subset_span
-/
theorem span_preimage_le (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M₂) :
    span R (f ⁻¹' s) <= (span R₂ s).comap f := by
  rw [span_le]; rw [comap_coe]
  exact preimage_mono subset_span

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le

include σ₁₂ in
/--
theorem `mapsTo_span` / 定理 `mapsTo_span`

English:
theorem mapsTo_span
  given: {f : M ->ₛₗ[σ₁₂] M₂} {s : Set M} {t : Set M₂} (h : MapsTo f s t)
  proof: (span_mono h).trans (span_preimage_le (σ₁₂ := σ₁₂) f t)

alias _root_.Set.MapsTo.submoduleSpan := mapsTo_span

中文:
定理 mapsTo_span
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {s : 集合 M} {t : 集合 M₂} (h : 映射到 f s t)
  证明: (span_mono h).trans (span_preimage_le (σ₁₂ := σ₁₂) f t)

alias _root_.Set.MapsTo.submoduleSpan := mapsTo_span

Depends on / 依赖: span_mono, span_preimage_le
-/
theorem mapsTo_span {f : M ->ₛₗ[σ₁₂] M₂} {s : Set M} {t : Set M₂} (h : MapsTo f s t) :
    MapsTo f (span R s) (span R₂ t) :=
  (span_mono h).trans (span_preimage_le (σ₁₂ := σ₁₂) f t)

alias _root_.Set.MapsTo.submoduleSpan := mapsTo_span

section

variable {N : Type*} [AddCommMonoid N] [Module R N]

/--
lemma `linearMap_eq_iff_of_eq_span` / 引理 `linearMap_eq_iff_of_eq_span`

English:
lemma linearMap_eq_iff_of_eq_span
  statement: {V : Submodule R M} (f g : V ->ₗ[R] N)
  proof: by
  constructor
  · rintro rfl _
    rfl
  · intro h
    subst hV
    suffices forall (x : M) (hx : x in span R S), f ⟨x, hx⟩ = g ⟨x, hx⟩ by
      ext ⟨x, hx⟩
      exact this x hx
    intro x hx
    induction hx using span_induction with
    | mem x hx => exact h ⟨x, hx⟩
    | zero => erw [map_zer

中文:
引理 linearMap_eq_iff_of_eq_span
  结论: {V : 子模 R M} (f g : V ->ₗ[R] N)
  证明: by
  constructor
  · rintro rfl _
    rfl
  · intro h
    subst hV
    suffices forall (x : M) (hx : x in span R S), f ⟨x, hx⟩ = g ⟨x, hx⟩ by
      ext ⟨x, hx⟩
      exact this x hx
    intro x hx
    induction hx using span_induction with
    | mem x hx => exact h ⟨x, hx⟩
    | zero => erw [map_zer

Depends on / 依赖: f.map_add, f.map_smul, g.map_add, g.map_smul, map_add, map_smul, map_zero, span_induction
-/
lemma linearMap_eq_iff_of_eq_span {V : Submodule R M} (f g : V ->ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = g ↔ forall (s : S), f ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ =
      g ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    subst hV
    suffices forall (x : M) (hx : x in span R S), f ⟨x, hx⟩ = g ⟨x, hx⟩ by
      ext ⟨x, hx⟩
      exact this x hx
    intro x hx
    induction hx using span_induction with
    | mem x hx => exact h ⟨x, hx⟩
    | zero => erw [map_zero, map_zero]
    | add x y hx hy hx' hy' =>
        erw [f.map_add ⟨x, hx⟩ ⟨y, hy⟩, g.map_add ⟨x, hx⟩ ⟨y, hy⟩]
        rw [hx']; rw [hy']
    | smul a x hx hx' =>
        erw [f.map_smul a ⟨x, hx⟩, g.map_smul a ⟨x, hx⟩]
        rw [hx']

/--
lemma `linearMap_eq_iff_of_span_eq_top` / 引理 `linearMap_eq_iff_of_span_eq_top`

English:
lemma linearMap_eq_iff_of_span_eq_top
  statement: (f g : M ->ₗ[R] N)
  proof: by
  convert!
    linearMap_eq_iff_of_eq_span (f.comp (Submodule.subtype _)) (g.comp (Submodule.subtype _))
      hM.symm
  constructor
  · rintro rfl
    rfl
  · intro h
    ext x
    exact DFunLike.congr_fun h ⟨x, by simp⟩

中文:
引理 linearMap_eq_iff_of_span_eq_top
  结论: (f g : M ->ₗ[R] N)
  证明: by
  convert!
    linearMap_eq_iff_of_eq_span (f.comp (Submodule.subtype _)) (g.comp (Submodule.subtype _))
      hM.symm
  constructor
  · rintro rfl
    rfl
  · intro h
    ext x
    exact DFunLike.congr_fun h ⟨x, by simp⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Submodule, Submodule.subtype, congr_fun, convert, f.comp, g.comp, hM.symm, linearMap_eq_iff_of_eq_span, subtype
-/
lemma linearMap_eq_iff_of_span_eq_top (f g : M ->ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = g ↔ forall (s : S), f s = g s := by
  convert!
    linearMap_eq_iff_of_eq_span (f.comp (Submodule.subtype _)) (g.comp (Submodule.subtype _))
      hM.symm
  constructor
  · rintro rfl
    rfl
  · intro h
    ext x
    exact DFunLike.congr_fun h ⟨x, by simp⟩

/--
lemma `linearMap_eq_zero_iff_of_span_eq_top` / 引理 `linearMap_eq_zero_iff_of_span_eq_top`

English:
lemma linearMap_eq_zero_iff_of_span_eq_top
  statement: (f : M ->ₗ[R] N)
  proof: linearMap_eq_iff_of_span_eq_top f 0 hM

中文:
引理 linearMap_eq_zero_iff_of_span_eq_top
  结论: (f : M ->ₗ[R] N)
  证明: linearMap_eq_iff_of_span_eq_top f 0 hM

Depends on / 依赖: linearMap_eq_iff_of_span_eq_top
-/
lemma linearMap_eq_zero_iff_of_span_eq_top (f : M ->ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = 0 ↔ forall (s : S), f s = 0 :=
  linearMap_eq_iff_of_span_eq_top f 0 hM

/--
lemma `linearMap_eq_zero_iff_of_eq_span` / 引理 `linearMap_eq_zero_iff_of_eq_span`

English:
lemma linearMap_eq_zero_iff_of_eq_span
  statement: {V : Submodule R M} (f : V ->ₗ[R] N)
  proof: linearMap_eq_iff_of_eq_span f 0 hV

中文:
引理 linearMap_eq_zero_iff_of_eq_span
  结论: {V : 子模 R M} (f : V ->ₗ[R] N)
  证明: linearMap_eq_iff_of_eq_span f 0 hV

Depends on / 依赖: linearMap_eq_iff_of_eq_span
-/
lemma linearMap_eq_zero_iff_of_eq_span {V : Submodule R M} (f : V ->ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = 0 ↔ forall (s : S), f ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ = 0 :=
  linearMap_eq_iff_of_eq_span f 0 hV

end

/--
theorem `span_smul_eq_of_isUnit` / 定理 `span_smul_eq_of_isUnit`

English:
theorem span_smul_eq_of_isUnit
  given: (s : Set M) (r : R) (hr : IsUnit r)
  statement: span R (r • s) = span R s
  proof: by
  apply le_antisymm
  · apply span_smul_le
  · convert! span_smul_le (r • s) ((hr.unit⁻¹ :) : R)
    simp [smul_smul]

中文:
定理 span_smul_eq_of_isUnit
  条件: (s : 集合 M) (r : R) (hr : 是单位 r)
  结论: span R (r • s) = span R s
  证明: by
  apply le_antisymm
  · apply span_smul_le
  · convert! span_smul_le (r • s) ((hr.unit⁻¹ :) : R)
    simp [smul_smul]

Depends on / 依赖: convert, hr.unit, le_antisymm, smul_smul, span_smul_le
-/
theorem span_smul_eq_of_isUnit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s) = span R s := by
  apply le_antisymm
  · apply span_smul_le
  · convert! span_smul_le (r • s) ((hr.unit⁻¹ :) : R)
    simp [smul_smul]

/--
theorem `coe_scott_continuous` / 定理 `coe_scott_continuous`

English:
theorem coe_scott_continuous
  proof: OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
    ⟨SetLike.coe_mono, fun _ => coe_iSup_of_chain _⟩

中文:
定理 coe_scott_continuous
  证明: OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
    ⟨SetLike.coe_mono, fun _ => coe_iSup_of_chain _⟩

Depends on / 依赖: OmegaCompletePartialOrder, ScottContinuous.of_monotone_map_, SetLike, SetLike.coe_mono, coe_iSup_of_chain, coe_mono
-/
theorem coe_scott_continuous :
    OmegaCompletePartialOrder.ωScottContinuous ((↑) : Submodule R M -> Set M) :=
  OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
    ⟨SetLike.coe_mono, fun _ => coe_iSup_of_chain _⟩

section IsScalarTower

variable (S)

variable [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] (p : Submodule R M)

/--
Definition of `inclusionSpan` / `inclusionSpan` 的定义

English:
definition inclusionSpan
  signature: :
  body: ⟨x, subset_span x.property⟩
  map_add' x y := by simp
  map_smul' t x := by simp

中文:
定义 inclusionSpan
  签名: :
  定义体: ⟨x, subset_span x.property⟩
  map_add' x y := by simp
  map_smul' t x := by simp
-/
@[simps] def inclusionSpan :
    p ->ₗ[R] span S (p : Set M) where
  toFun x := ⟨x, subset_span x.property⟩
  map_add' x y := by simp
  map_smul' t x := by simp

/--
lemma `injective_inclusionSpan` / 引理 `injective_inclusionSpan`

English:
lemma injective_inclusionSpan
  proof: by
  intro x y hxy
  rw [Subtype.ext_iff] at hxy
  simpa using hxy

中文:
引理 injective_inclusionSpan
  证明: by
  intro x y hxy
  rw [Subtype.ext_iff] at hxy
  simpa using hxy

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
lemma injective_inclusionSpan :
    Injective (p.inclusionSpan S) := by
  intro x y hxy
  rw [Subtype.ext_iff] at hxy
  simpa using hxy

/--
lemma `span_range_inclusionSpan` / 引理 `span_range_inclusionSpan`

English:
lemma span_range_inclusionSpan
  proof: by
  have : (span S (p : Set M)).subtype '' range (inclusionSpan S p) = p := by
    ext; simpa [Subtype.ext_iff] using! fun h => subset_span h
  apply map_injective_of_injective (span S (p : Set M)).injective_subtype
  rw [map_subtype_top]; rw [map_span]; rw [this]

中文:
引理 span_range_inclusionSpan
  证明: by
  have : (span S (p : Set M)).subtype '' range (inclusionSpan S p) = p := by
    ext; simpa [Subtype.ext_iff] using! fun h => subset_span h
  apply map_injective_of_injective (span S (p : Set M)).injective_subtype
  rw [map_subtype_top]; rw [map_span]; rw [this]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, inclusionSpan, injective_subtype, map_injective_of_injective, map_span, map_subtype_top, subset_span, subtype
-/
lemma span_range_inclusionSpan :
    span S (range <| p.inclusionSpan S) = ⊤ := by
  have : (span S (p : Set M)).subtype '' range (inclusionSpan S p) = p := by
    ext; simpa [Subtype.ext_iff] using! fun h => subset_span h
  apply map_injective_of_injective (span S (p : Set M)).injective_subtype
  rw [map_subtype_top]; rw [map_span]; rw [this]

variable (R s)

/--
theorem `span_le_restrictScalars` / 定理 `span_le_restrictScalars`

English:
theorem span_le_restrictScalars
  proof: Submodule.span_le.2 Submodule.subset_span

中文:
定理 span_le_restrictScalars
  证明: Submodule.span_le.2 Submodule.subset_span

Depends on / 依赖: Submodule, Submodule.span_le, Submodule.subset_span, span_le, subset_span
-/
theorem span_le_restrictScalars :
    span R s <= (span S s).restrictScalars R :=
  Submodule.span_le.2 Submodule.subset_span

/-- A version of `Submodule.span_le_restrictScalars` with coercions. -/
@[simp]
/--
theorem `span_subset_span` / 定理 `span_subset_span`

English:
theorem span_subset_span
  proof: span_le_restrictScalars R S s

中文:
定理 span_subset_span
  证明: span_le_restrictScalars R S s

Depends on / 依赖: span_le_restrictScalars
-/
theorem span_subset_span :
    ↑(span R s) subseteq (span S s : Set M) :=
  span_le_restrictScalars R S s

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
@[simp]
/--
theorem `span_span_of_tower` / 定理 `span_span_of_tower`

English:
theorem span_span_of_tower
  proof: le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)

中文:
定理 span_span_of_tower
  证明: le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)

Depends on / 依赖: le_antisymm, span_le, span_mono, span_subset_span, subset_span
-/
theorem span_span_of_tower :
    span S (span R s : Set M) = span S s :=
  le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)

/--
theorem `span_eq_top_of_span_eq_top` / 定理 `span_eq_top_of_span_eq_top`

English:
theorem span_eq_top_of_span_eq_top
  given: (s : Set M) (hs : span R s = ⊤)
  statement: span S s = ⊤
  proof: le_top.antisymm (hs.ge.trans (span_le_restrictScalars R S s))

中文:
定理 span_eq_top_of_span_eq_top
  条件: (s : 集合 M) (hs : span R s = ⊤)
  结论: span S s = ⊤
  证明: le_top.antisymm (hs.ge.trans (span_le_restrictScalars R S s))

Depends on / 依赖: antisymm, hs.ge.trans, le_top, le_top.antisymm, span_le_restrictScalars
-/
theorem span_eq_top_of_span_eq_top (s : Set M) (hs : span R s = ⊤) : span S s = ⊤ :=
  le_top.antisymm (hs.ge.trans (span_le_restrictScalars R S s))

set_option backward.isDefEq.respectTransparency false in
variable {R S} in
/--
lemma `span_range_inclusion_eq_top` / 引理 `span_range_inclusion_eq_top`

English:
lemma span_range_inclusion_eq_top
  statement: (p : Submodule R M) (q : Submodule S M)
  proof: by
  suffices (span S (range (inclusion h₁))).map q.subtype = q by
    apply map_injective_of_injective q.injective_subtype
    rw [this]; rw [q.map_subtype_top]
  rw [map_span]
  suffices q.subtype '' ((LinearMap.range (inclusion h₁)) : Set <| q.restrictScalars R) = p by
    refine this ▸ le_antisy

中文:
引理 span_range_inclusion_eq_top
  结论: (p : 子模 R M) (q : 子模 S M)
  证明: by
  suffices (span S (range (inclusion h₁))).map q.subtype = q by
    apply map_injective_of_injective q.injective_subtype
    rw [this]; rw [q.map_subtype_top]
  rw [map_span]
  suffices q.subtype '' ((LinearMap.range (inclusion h₁)) : Set <| q.restrictScalars R) = p by
    refine this ▸ le_antisy

Depends on / 依赖: LinearMap, LinearMap.range, inclusion, injective_subtype, le_antisymm, map_injective_of_injective, map_span, map_subtype_top, q.injective_subtype, q.map_subtype_top, q.restrictScalars, q.subtype, range_inclusion, restrictScalars, span_mono, subtype
-/
lemma span_range_inclusion_eq_top (p : Submodule R M) (q : Submodule S M)
    (h₁ : p <= q.restrictScalars R) (h₂ : q <= span S p) :
    span S (range (inclusion h₁)) = ⊤ := by
  suffices (span S (range (inclusion h₁))).map q.subtype = q by
    apply map_injective_of_injective q.injective_subtype
    rw [this]; rw [q.map_subtype_top]
  rw [map_span]
  suffices q.subtype '' ((LinearMap.range (inclusion h₁)) : Set <| q.restrictScalars R) = p by
    refine this ▸ le_antisymm ?_ h₂
    simpa using span_mono (R := S) h₁
  ext x
  simpa [range_inclusion] using fun hx => h₁ hx

@[simp]
/--
theorem `span_range_inclusion_restrictScalars_eq_top` / 定理 `span_range_inclusion_restrictScalars_eq_top`

English:
theorem span_range_inclusion_restrictScalars_eq_top
  proof: span_range_inclusion_eq_top _ _ _ by simp

中文:
定理 span_range_inclusion_restrictScalars_eq_top
  证明: span_range_inclusion_eq_top _ _ _ by simp

Depends on / 依赖: span_range_inclusion_eq_top
-/
theorem span_range_inclusion_restrictScalars_eq_top :
    span S (range (inclusion <| span_le_restrictScalars R S s)) = ⊤ :=
span_range_inclusion_eq_top _ _ _ by simp

end IsScalarTower

/--
theorem `span_singleton_eq_span_singleton` / 定理 `span_singleton_eq_span_singleton`

English:
theorem span_singleton_eq_span_singleton
  statement: {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M]
  proof: by
  constructor
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    rcases eq_or_ne y 0 with rfl | hy; · simp
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    · apply smul_left_injective R hy
      simpa only [mul_smul, one_smul]
    · rw [← hb] at hy


中文:
定理 span_singleton_eq_span_singleton
  结论: {R M : 类型} [环 R] [是整环 R] [加法交换群 M]
  证明: by
  constructor
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    rcases eq_or_ne y 0 with rfl | hy; · simp
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    · apply smul_left_injective R hy
      simpa only [mul_smul, one_smul]
    · rw [← hb] at hy


Depends on / 依赖: eq_or_ne, le_antisymm_iff, mem_span_singleton, mul_smul, one_smul, smul_left_injective, smul_ne_zero_iff, span_singleton_group_smul_eq, span_singleton_le_iff_mem
-/
theorem span_singleton_eq_span_singleton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.IsTorsionFree R M] {x y : M} :
    (R ∙ x) = (R ∙ y) ↔ exists z : Rˣ, z • x = y := by
  constructor
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    rcases eq_or_ne y 0 with rfl | hy; · simp
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    · apply smul_left_injective R hy
      simpa only [mul_smul, one_smul]
    · rw [← hb] at hy
      apply smul_left_injective R (smul_ne_zero_iff.1 hy).2
      simp only [mul_smul, one_smul, hb]
  · rintro ⟨u, rfl⟩
    exact (span_singleton_group_smul_eq _ _ _).symm

@[simp]
/--
theorem `span_image` / 定理 `span_image`

English:
theorem span_image
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂)
  proof: (map_span f s).symm

@[simp]

中文:
定理 span_image
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂)
  证明: (map_span f s).symm

@[simp]

Depends on / 依赖: map_span
-/
theorem span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) :
    span R₂ (f '' s) = map f (span R s) :=
  (map_span f s).symm

@[simp]
/--
theorem `span_image_linearEquiv` / 定理 `span_image_linearEquiv`

English:
theorem span_image_linearEquiv
  statement: {σ₂₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  proof: span_image _

中文:
定理 span_image_linearEquiv
  结论: {σ₂₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  证明: span_image _

Depends on / 依赖: span_image
-/
theorem span_image_linearEquiv {σ₂₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : M ≃ₛₗ[σ₁₂] M₂) : span R₂ (f '' s) = map (f : M ->ₛₗ[σ₁₂] M₂) (span R s) :=
  span_image _

/--
theorem `apply_mem_span_image_of_mem_span` / 定理 `apply_mem_span_image_of_mem_span`

English:
theorem apply_mem_span_image_of_mem_span
  statement: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
  proof: by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h

中文:
定理 apply_mem_span_image_of_mem_span
  结论: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
  证明: by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h

Depends on / 依赖: Submodule, Submodule.mem_map_of_mem, Submodule.span_image, mem_map_of_mem, span_image
-/
theorem apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
    {s : Set M} (h : x in Submodule.span R s) : f x in Submodule.span R₂ (f '' s) := by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h

/--
theorem `apply_mem_span_image_iff_mem_span` / 定理 `apply_mem_span_image_iff_mem_span`

English:
theorem apply_mem_span_image_iff_mem_span
  statement: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M}
  proof: by
  rw [← Submodule.mem_comap]; rw [← Submodule.map_span]; rw [Submodule.comap_map_eq_of_injective hf]

@[simp]

中文:
定理 apply_mem_span_image_iff_mem_span
  结论: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M}
  证明: by
  rw [← Submodule.mem_comap]; rw [← Submodule.map_span]; rw [Submodule.comap_map_eq_of_injective hf]

@[simp]

Depends on / 依赖: Submodule, Submodule.comap_map_eq_of_injective, Submodule.map_span, Submodule.mem_comap, comap_map_eq_of_injective, map_span, mem_comap
-/
theorem apply_mem_span_image_iff_mem_span [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M}
    {s : Set M} (hf : Function.Injective f) :
    f x in Submodule.span R₂ (f '' s) ↔ x in Submodule.span R s := by
  rw [← Submodule.mem_comap]; rw [← Submodule.map_span]; rw [Submodule.comap_map_eq_of_injective hf]

@[simp]
/--
theorem `map_subtype_span_singleton` / 定理 `map_subtype_span_singleton`

English:
theorem map_subtype_span_singleton
  given: {p : Submodule R M} (x : p)
  proof: by simp [← span_image]

中文:
定理 map_subtype_span_singleton
  条件: {p : 子模 R M} (x : p)
  证明: by simp [← span_image]

Depends on / 依赖: span_image
-/
theorem map_subtype_span_singleton {p : Submodule R M} (x : p) :
    map p.subtype (R ∙ x) = R ∙ (x : M) := by simp [← span_image]

/--
theorem `notMem_span_of_apply_notMem_span_image` / 定理 `notMem_span_of_apply_notMem_span_image`

English:
theorem notMem_span_of_apply_notMem_span_image
  statement: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
  proof: h.imp (apply_mem_span_image_of_mem_span f)

中文:
定理 notMem_span_of_apply_notMem_span_image
  结论: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
  证明: h.imp (apply_mem_span_image_of_mem_span f)

Depends on / 依赖: apply_mem_span_image_of_mem_span, h.imp
-/
theorem notMem_span_of_apply_notMem_span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M}
    {s : Set M} (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submodule.span R s :=
  h.imp (apply_mem_span_image_of_mem_span f)

section DistribMulAction

variable {α : Type*} [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/--
theorem `smul_span` / 定理 `smul_span`

English:
theorem smul_span
  given: (a : α) (s : Set M)
  statement: a • span R s = span R (a • s)
  proof: map_span _ _

中文:
定理 smul_span
  条件: (a : α) (s : 集合 M)
  结论: a • span R s = span R (a • s)
  证明: map_span _ _

Depends on / 依赖: map_span
-/
theorem smul_span (a : α) (s : Set M) : a • span R s = span R (a • s) :=
  map_span _ _

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (a : α) (S : Submodule R M)
  statement: a • S = span R (a • S)
  proof: by
  simp [← smul_span]

中文:
引理 smul_def
  条件: (a : α) (S : 子模 R M)
  结论: a • S = span R (a • S)
  证明: by
  simp [← smul_span]

Depends on / 依赖: smul_span
-/
lemma smul_def (a : α) (S : Submodule R M) : a • S = span R (a • S) := by
  simp [← smul_span]

/--
theorem `span_smul` / 定理 `span_smul`

English:
theorem span_smul
  given: (a : α) (s : Set M)
  statement: span R (a • s) = a • span R s
  proof: Eq.symm (span_image _).symm

中文:
定理 span_smul
  条件: (a : α) (s : 集合 M)
  结论: span R (a • s) = a • span R s
  证明: Eq.symm (span_image _).symm

Depends on / 依赖: Eq.symm, span_image
-/
theorem span_smul (a : α) (s : Set M) : span R (a • s) = a • span R s :=
  Eq.symm (span_image _).symm

/--
theorem `set_smul_span` / 定理 `set_smul_span`

English:
theorem set_smul_span
  given: (s : Set α) (t : Set M)
  proof: by
  simp_rw [set_smul_eq_iSup, smul_span, iSup_span, Set.iUnion_smul_set]

中文:
定理 set_smul_span
  条件: (s : 集合 α) (t : 集合 M)
  证明: by
  simp_rw [set_smul_eq_iSup, smul_span, iSup_span, Set.iUnion_smul_set]

Depends on / 依赖: Set.iUnion_smul_set, iSup_span, iUnion_smul_set, set_smul_eq_iSup, simp_rw, smul_span
-/
theorem set_smul_span (s : Set α) (t : Set M) :
    s • span R t = span R (s • t) := by
  simp_rw [set_smul_eq_iSup, smul_span, iSup_span, Set.iUnion_smul_set]

/--
theorem `span_set_smul` / 定理 `span_set_smul`

English:
theorem span_set_smul
  given: (s : Set α) (t : Set M)
  proof: (set_smul_span s t).symm

中文:
定理 span_set_smul
  条件: (s : 集合 α) (t : 集合 M)
  证明: (set_smul_span s t).symm

Depends on / 依赖: set_smul_span
-/
theorem span_set_smul (s : Set α) (t : Set M) :
    span R (s • t) = s • span R t := (set_smul_span s t).symm

end DistribMulAction

/--
theorem `iSup_toAddSubmonoid` / 定理 `iSup_toAddSubmonoid`

English:
theorem iSup_toAddSubmonoid
  given: {ι : Sort*} (p : ι -> Submodule R M)
  proof: by
  refine le_antisymm (fun x => ?_) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  intro hx
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun r x _ hx => ?

中文:
定理 iSup_toAddSubmonoid
  条件: {ι : 类型层*} (p : ι -> 子模 R M)
  证明: by
  refine le_antisymm (fun x => ?_) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  intro hx
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun r x _ hx => ?

Depends on / 依赖: AddSubmonoid, AddSubmonoid.add_mem, AddSubmonoid.closure_induction, AddSubmonoid.iSup_eq_closure, AddSubmonoid.subset_closure, AddSubmonoid.zero_mem, Submodule, Submodule.span_induction, add_mem, closure_induction, coe_toAddSubmonoid, iSup_eq_closure, iSup_eq_span, iSup_le, le_antisymm, le_iSup, mem_toAddSubmonoid, simp_rw, span_induction, subset_closure
-/
theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι -> Submodule R M) :
    (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid := by
  refine le_antisymm (fun x => ?_) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  intro hx
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun r x _ hx => ?_) hx
  · exact AddSubmonoid.subset_closure hx
  · exact AddSubmonoid.zero_mem _
  · exact AddSubmonoid.add_mem _ hx hy
  · refine AddSubmonoid.closure_induction ?_ ?_ ?_ hx
    · rintro x ⟨_, ⟨i, rfl⟩, hix : x in p i⟩
      apply AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨i, _⟩)
      exact smul_mem _ r hix
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _
    · intro x y _ _ hx hy
      rw [smul_add]
      exact AddSubmonoid.add_mem _ hx hy

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_elim]
/--
theorem `iSup_induction` / 定理 `iSup_induction`

English:
theorem iSup_induction
  statement: {ι : Sort*} (p : ι -> Submodule R M) {motive : M -> Prop} {x : M}
  proof: by
  rw [← mem_toAddSubmonoid]; rw [iSup_toAddSubmonoid] at hx
  exact AddSubmonoid.iSup_induction (x := x) _ hx mem zero add

中文:
定理 iSup_induction
  结论: {ι : 类型层*} (p : ι -> 子模 R M) {motive : M -> 命题} {x : M}
  证明: by
  rw [← mem_toAddSubmonoid]; rw [iSup_toAddSubmonoid] at hx
  exact AddSubmonoid.iSup_induction (x := x) _ hx mem zero add

Depends on / 依赖: AddSubmonoid, AddSubmonoid.iSup_induction, iSup_induction, iSup_toAddSubmonoid, mem_toAddSubmonoid
-/
theorem iSup_induction {ι : Sort*} (p : ι -> Submodule R M) {motive : M -> Prop} {x : M}
    (hx : x in ⨆ i, p i) (mem : forall (i), forall x in p i, motive x) (zero : motive 0)
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive x := by
  rw [← mem_toAddSubmonoid]; rw [iSup_toAddSubmonoid] at hx
  exact AddSubmonoid.iSup_induction (x := x) _ hx mem zero add

/-- A dependent version of `submodule.iSup_induction`. -/
@[elab_as_elim]
/--
theorem `iSup_induction'` / 定理 `iSup_induction'`

English:
theorem iSup_induction'
  statement: {ι : Sort*} (p : ι -> Submodule R M) {motive : forall x, (x in ⨆ i, p i) -> Prop}
  proof: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, p i) (hc : motive x hx) => hc
  refine iSup_induction p (motive := fun x : M => exists (hx : x in ⨆ i, p i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, a

中文:
定理 iSup_induction'
  结论: {ι : 类型层*} (p : ι -> 子模 R M) {motive : 对任意 x, (x in ⨆ i, p i) -> 命题}
  证明: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, p i) (hc : motive x hx) => hc
  refine iSup_induction p (motive := fun x : M => exists (hx : x in ⨆ i, p i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, a

Depends on / 依赖: Exists, Exists.elim, iSup_induction, motive
-/
theorem iSup_induction' {ι : Sort*} (p : ι -> Submodule R M) {motive : forall x, (x in ⨆ i, p i) -> Prop}
    (mem : forall (i) (x) (hx : x in p i), motive x (mem_iSup_of_mem i hx)) (zero : motive 0 (zero_mem _))
    (add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x in ⨆ i, p i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, p i) (hc : motive x hx) => hc
  refine iSup_induction p (motive := fun x : M => exists (hx : x in ⨆ i, p i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

/--
theorem `singleton_span_isCompactElement` / 定理 `singleton_span_isCompactElement`

English:
theorem singleton_span_isCompactElement
  given: (x : M)
  proof: by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro d hemp hdir hsup
  have : x in (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subse

中文:
定理 singleton_span_isCompactElement
  条件: (x : M)
  证明: by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro d hemp hdir hsup
  have : x in (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subse

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le, SetLike, SetLike.le_def.mp, isCompactElement_iff_le_of_directed_sSup_le, le_def, mem_sSup_of_directed, mem_span_singleton_self, singleton_subset_iff, span_le
-/
theorem singleton_span_isCompactElement (x : M) :
    IsCompactElement (span R {x} : Submodule R M) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro d hemp hdir hsup
  have : x in (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff] ⟩⟩

/--
theorem `finset_span_isCompactElement` / 定理 `finset_span_isCompactElement`

English:
theorem finset_span_isCompactElement
  given: (S : Finset M)
  proof: by
  rw [span_eq_iSup_of_singleton_spans]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup]
  exact
    CompleteLattice.isCompactElement_finsetSup S fun x _ => singleton_span_isCompactElement x

中文:
定理 finset_span_isCompactElement
  条件: (S : 有限集 M)
  证明: by
  rw [span_eq_iSup_of_singleton_spans]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup]
  exact
    CompleteLattice.isCompactElement_finsetSup S fun x _ => singleton_span_isCompactElement x

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_finsetSup, Finset, Finset.mem_coe, Finset.sup_eq_iSup, isCompactElement_finsetSup, mem_coe, singleton_span_isCompactElement, span_eq_iSup_of_singleton_spans, sup_eq_iSup
-/
theorem finset_span_isCompactElement (S : Finset M) :
    IsCompactElement (span R S : Submodule R M) := by
  rw [span_eq_iSup_of_singleton_spans]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup]
  exact
    CompleteLattice.isCompactElement_finsetSup S fun x _ => singleton_span_isCompactElement x

/--
theorem `finite_span_isCompactElement` / 定理 `finite_span_isCompactElement`

English:
theorem finite_span_isCompactElement
  given: (S : Set M) (h : S.Finite)
  proof: Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset

中文:
定理 finite_span_isCompactElement
  条件: (S : 集合 M) (h : S.有限)
  证明: Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset

Depends on / 依赖: Finite, Finite.coe_toFinset, coe_toFinset, finset_span_isCompactElement, h.toFinset, toFinset
-/
theorem finite_span_isCompactElement (S : Set M) (h : S.Finite) :
    IsCompactElement (span R S : Submodule R M) :=
  Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCompactlyGenerated (Submodule R M)
  body: ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases (Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        apply singleton_span_isCompactElement, by
        rw [sSup_eq_iSup]; rw [iSup_image]; rw [← span_eq_iSup_of_singleton_spans]; rw [span_eq]⟩⟩⟩

中文:
实例 :
  签名: 是余mpactlyGenerated (子模 R M)
  定义体: ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases (Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        apply singleton_span_isCompactElement, by
        rw [sSup_eq_iSup]; rw [iSup_image]; rw [← span_eq_iSup_of_singleton_spans]; rw [span_eq]⟩⟩⟩

Depends on / 依赖: Set.mem_image, iSup_image, mem_image, sSup_eq_iSup, singleton_span_isCompactElement, span_eq, span_eq_iSup_of_singleton_spans
-/
instance : IsCompactlyGenerated (Submodule R M) :=
  ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases (Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        apply singleton_span_isCompactElement, by
        rw [sSup_eq_iSup]; rw [iSup_image]; rw [← span_eq_iSup_of_singleton_spans]; rw [span_eq]⟩⟩⟩

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] (q₁ q₁' : Submodule R M')

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Submodule R (M × M')
  body: { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]

中文:
定义 乘积
  签名: : 子模 R (M × M')
  定义体: { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]

Depends on / 依赖: carrier, p.toAddSubmonoid.prod, smul_mem, toAddSubmonoid
-/
def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]
/--
theorem `prod_coe` / 定理 `prod_coe`

English:
theorem prod_coe
  statement: (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M')
  proof: rfl

@[simp]

中文:
定理 prod_coe
  结论: (乘积 p q₁ : 集合 (M × M')) = (p : 集合 M) ×ˢ (q₁ : 集合 M')
  证明: rfl

@[simp]
-/
theorem prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M') :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {p : Submodule R M} {q : Submodule R M'} {x : M × M'}
  proof: Set.mem_prod

中文:
定理 mem_prod
  条件: {p : 子模 R M} {q : 子模 R M'} {x : M × M'}
  证明: Set.mem_prod

Depends on / 依赖: Set.mem_prod, mem_prod
-/
theorem mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} :
    x in prod p q ↔ x.1 in p ∧ x.2 in q :=
  Set.mem_prod

/--
theorem `span_prod_le` / 定理 `span_prod_le`

English:
theorem span_prod_le
  given: (s : Set M) (t : Set M')
  statement: span R (s ×ˢ t) <= prod (span R s) (span R t)
  proof: span_le.2 Set.prod_mono subset_span subset_span

@[simp]

中文:
定理 span_prod_le
  条件: (s : 集合 M) (t : 集合 M')
  结论: span R (s ×ˢ t) <= 乘积 (span R s) (span R t)
  证明: span_le.2 Set.prod_mono subset_span subset_span

@[simp]

Depends on / 依赖: Set.prod_mono, prod_mono, span_le, subset_span
-/
theorem span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) <= prod (span R s) (span R t) :=
span_le.2 Set.prod_mono subset_span subset_span

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤
  proof: by ext; simp

@[simp]

中文:
定理 prod_top
  结论: (乘积 ⊤ ⊤ : 子模 R (M × M')) = ⊤
  证明: by ext; simp

@[simp]
-/
theorem prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤ := by ext; simp

@[simp]
/--
theorem `prod_bot` / 定理 `prod_bot`

English:
theorem prod_bot
  statement: (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
  proof: by ext ⟨x, y⟩; simp

中文:
定理 prod_bot
  结论: (乘积 ⊥ ⊥ : 子模 R (M × M')) = ⊥
  证明: by ext ⟨x, y⟩; simp
-/
theorem prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥ := by ext ⟨x, y⟩; simp

/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {p p' : Submodule R M} {q q' : Submodule R M'}
  proof: Set.prod_mono

@[simp]

中文:
定理 prod_mono
  条件: {p p' : 子模 R M} {q q' : 子模 R M'}
  证明: Set.prod_mono

@[simp]

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} :
    p <= p' -> q <= q' -> prod p q <= prod p' q' :=
  Set.prod_mono

@[simp]
/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  statement: prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁')
  proof: SetLike.coe_injective Set.prod_inter_prod

@[simp]

中文:
定理 prod_inf_prod
  结论: 乘积 p q₁ ⊓ 乘积 p' q₁' = 乘积 (p ⊓ p') (q₁ ⊓ q₁')
  证明: SetLike.coe_injective Set.prod_inter_prod

@[simp]

Depends on / 依赖: Set.prod_inter_prod, SetLike, SetLike.coe_injective, coe_injective, prod_inter_prod
-/
theorem prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
  SetLike.coe_injective Set.prod_inter_prod

@[simp]
/--
theorem `prod_sup_prod` / 定理 `prod_sup_prod`

English:
theorem prod_sup_prod
  statement: prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁')
  proof: by
  refine le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) ?_
  simp only [SetLike.le_def, mem_prod, and_imp, Prod.forall]; intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  ex

中文:
定理 prod_sup_prod
  结论: 乘积 p q₁ ⊔ 乘积 p' q₁' = 乘积 (p ⊔ p') (q₁ ⊔ q₁')
  证明: by
  refine le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) ?_
  simp only [SetLike.le_def, mem_prod, and_imp, Prod.forall]; intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  ex

Depends on / 依赖: Prod.forall, SetLike, SetLike.le_def, and_imp, le_antisymm, le_def, le_sup_left, le_sup_right, mem_prod, mem_sup, prod_mono, sup_le
-/
theorem prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') := by
  refine le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) ?_
  simp only [SetLike.le_def, mem_prod, and_imp, Prod.forall]; intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  exact mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩

/--
lemma `_root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span` / 引理 `_root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span`

English:
lemma _root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span
  statement: {R M N P : Type*} [CommSemiring R]
  proof: by
  induction hx, hy using span_induction₂ with
  | mem_mem u v hu hv => exact hB u hu v hv
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u₁ u₂ v hu₁ hu₂ hv huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | add_right u v₁ v₂ hu hv₁ hv₂ huv₁ huv₂ => simpa using add_mem huv₁ huv₂
 

中文:
引理 _root_.线性映射.BilinMap.apply_apply_mem_of_mem_span
  结论: {R M N P : 类型} [交换半环 R]
  证明: by
  induction hx, hy using span_induction₂ with
  | mem_mem u v hu hv => exact hB u hu v hv
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u₁ u₂ v hu₁ hu₂ hv huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | add_right u v₁ v₂ hu hv₁ hv₂ huv₁ huv₂ => simpa using add_mem huv₁ huv₂
 

Depends on / 依赖: Submodule, Submodule.smul_mem, add_left, add_mem, add_right, mem_mem, smul_left, smul_mem, smul_right, zero_left, zero_right
-/
lemma _root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (P' : Submodule R P) (s : Set M) (t : Set N)
    (B : M ->ₗ[R] N ->ₗ[R] P) (hB : forall x in s, forall y in t, B x y in P')
    (x : M) (y : N) (hx : x in span R s) (hy : y in span R t) :
    B x y in P' := by
  induction hx, hy using span_induction₂ with
  | mem_mem u v hu hv => exact hB u hu v hv
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u₁ u₂ v hu₁ hu₂ hv huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | add_right u v₁ v₂ hu hv₁ hv₂ huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | smul_left t u v hu hv huv => simpa using Submodule.smul_mem _ _ huv
  | smul_right t u v hu hv huv => simpa using Submodule.smul_mem _ _ huv

@[simp]
/--
lemma `biSup_comap_subtype_eq_top` / 引理 `biSup_comap_subtype_eq_top`

English:
lemma biSup_comap_subtype_eq_top
  given: {ι : Type*} (s : Set ι) (p : ι -> Submodule R M)
  proof: by
  refine eq_top_iff.mpr fun ⟨x, hx⟩ _ => ?_
  suffices x in (⨆ i in s, (p i).comap (⨆ i in s, p i).subtype).map (⨆ i in s, (p i)).subtype by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp this
    exact hy
  suffices forall i in s, (comap (⨆ i in s, p i).subtype (p i)).map (⨆ i in s, p i).subtyp

中文:
引理 biSup_comap_subtype_eq_top
  条件: {ι : 类型} (s : 集合 ι) (p : ι -> 子模 R M)
  证明: by
  refine eq_top_iff.mpr fun ⟨x, hx⟩ _ => ?_
  suffices x in (⨆ i in s, (p i).comap (⨆ i in s, p i).subtype).map (⨆ i in s, (p i)).subtype by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp this
    exact hy
  suffices forall i in s, (comap (⨆ i in s, p i).subtype (p i)).map (⨆ i in s, p i).subtyp

Depends on / 依赖: Submodule, Submodule.mem_map.mp, biSup_congr, eq_top_iff, eq_top_iff.mpr, inf_eq_right, le_biSup, map_comap_eq, map_iSup, mem_map, range_subtype, subtype
-/
lemma biSup_comap_subtype_eq_top {ι : Type*} (s : Set ι) (p : ι -> Submodule R M) :
    ⨆ i in s, (p i).comap (⨆ i in s, p i).subtype = ⊤ := by
  refine eq_top_iff.mpr fun ⟨x, hx⟩ _ => ?_
  suffices x in (⨆ i in s, (p i).comap (⨆ i in s, p i).subtype).map (⨆ i in s, (p i)).subtype by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp this
    exact hy
  suffices forall i in s, (comap (⨆ i in s, p i).subtype (p i)).map (⨆ i in s, p i).subtype = p i by
    simpa only [map_iSup, biSup_congr this]
  intro i hi
  rw [map_comap_eq]; rw [range_subtype]; rw [inf_eq_right]
  exact le_biSup p hi

/--
theorem `_root_.LinearMap.exists_ne_zero_of_sSup_eq` / 定理 `_root_.LinearMap.exists_ne_zero_of_sSup_eq`

English:
theorem _root_.LinearMap.exists_ne_zero_of_sSup_eq
  statement: {N : Submodule R M} {f : N ->ₛₗ[σ₁₂] M₂}
  proof: have ⟨_, ⟨m, hm, rfl⟩, ne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top h (comap N.subtype '' s)
    by rw [sSup_eq_iSup] at hs; rw [sSup_image, ← hs, biSup_comap_subtype_eq_top]
  ⟨m, hm, fun eq => ne (LinearMap.ext fun x => congr($eq ⟨x, x.2⟩))⟩

中文:
定理 _root_.线性映射.存在_ne_zero_of_sSup_eq
  结论: {N : 子模 R M} {f : N ->ₛₗ[σ₁₂] M₂}
  证明: have ⟨_, ⟨m, hm, rfl⟩, ne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top h (comap N.subtype '' s)
    by rw [sSup_eq_iSup] at hs; rw [sSup_image, ← hs, biSup_comap_subtype_eq_top]
  ⟨m, hm, fun eq => ne (LinearMap.ext fun x => congr($eq ⟨x, x.2⟩))⟩

Depends on / 依赖: LinearMap, LinearMap.exists_ne_zero_of_sSup_eq_top, LinearMap.ext, N.subtype, biSup_comap_subtype_eq_top, exists_ne_zero_of_sSup_eq_top, sSup_eq_iSup, sSup_image, subtype
-/
theorem _root_.LinearMap.exists_ne_zero_of_sSup_eq {N : Submodule R M} {f : N ->ₛₗ[σ₁₂] M₂}
    (h : f != 0) (s : Set (Submodule R M)) (hs : sSup s = N):
    exists m, exists h : m in s, f ∘ₛₗ inclusion ((le_sSup h).trans_eq hs) != 0 :=
have ⟨_, ⟨m, hm, rfl⟩, ne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top h (comap N.subtype '' s)
    by rw [sSup_eq_iSup] at hs; rw [sSup_image, ← hs, biSup_comap_subtype_eq_top]
  ⟨m, hm, fun eq => ne (LinearMap.ext fun x => congr($eq ⟨x, x.2⟩))⟩

/--
lemma `span_val_image_eq_iff` / 引理 `span_val_image_eq_iff`

English:
lemma span_val_image_eq_iff
  given: (p : Submodule R M) (s : Set p)
  proof: by
  simp [← (Submodule.map_injective_of_injective p.injective_subtype).eq_iff, Submodule.map_span]

中文:
引理 span_val_image_eq_iff
  条件: (p : 子模 R M) (s : 集合 p)
  证明: by
  simp [← (Submodule.map_injective_of_injective p.injective_subtype).eq_iff, Submodule.map_span]

Depends on / 依赖: Submodule, Submodule.map_injective_of_injective, Submodule.map_span, eq_iff, injective_subtype, map_injective_of_injective, map_span, p.injective_subtype
-/
lemma span_val_image_eq_iff (p : Submodule R M) (s : Set p) :
    span R (Subtype.val '' s) = p ↔ span R s = ⊤ := by
  simp [← (Submodule.map_injective_of_injective p.injective_subtype).eq_iff, Submodule.map_span]

/--
lemma `span_range_subtype_eq_top_iff` / 引理 `span_range_subtype_eq_top_iff`

English:
lemma span_range_subtype_eq_top_iff
  statement: {ι : Type*} (p : Submodule R M) {s : ι -> M}
  proof: by
  simp [← span_val_image_eq_iff, ← Set.range_comp, Function.comp_def]

中文:
引理 span_range_subtype_eq_top_iff
  结论: {ι : 类型} (p : 子模 R M) {s : ι -> M}
  证明: by
  simp [← span_val_image_eq_iff, ← Set.range_comp, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, comp_def, range_comp, span_val_image_eq_iff
-/
lemma span_range_subtype_eq_top_iff {ι : Type*} (p : Submodule R M) {s : ι -> M}
    (hs : forall i, s i in p) :
    span R (Set.range fun i => (⟨s i, hs i⟩ : p)) = ⊤ ↔ span R (Set.range s) = p := by
  simp [← span_val_image_eq_iff, ← Set.range_comp, Function.comp_def]

/--
lemma `comap_le_comap_iff_of_le_range` / 引理 `comap_le_comap_iff_of_le_range`

English:
lemma comap_le_comap_iff_of_le_range
  statement: {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂]
  proof: by
  rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_comap_eq_of_le hp]

中文:
引理 comap_le_comap_iff_of_le_range
  结论: {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂]
  证明: by
  rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_comap_eq_of_le hp]

Depends on / 依赖: Submodule, Submodule.map_comap_eq_of_le, Submodule.map_le_iff_le_comap, map_comap_eq_of_le, map_le_iff_le_comap
-/
lemma comap_le_comap_iff_of_le_range {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂]
    {p q : Submodule R₂ M₂} (hp : p <= LinearMap.range f) :
    p.comap f <= q.comap f ↔ p <= q := by
  rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_comap_eq_of_le hp]

/--
lemma `comap_sup_of_injective` / 引理 `comap_sup_of_injective`

English:
lemma comap_sup_of_injective
  statement: {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂] {p q : Submodule R₂ M₂}
  proof: by
  apply map_injective_of_injective hf
  rw [map_sup]; rw [map_comap_eq_self]; rw [map_comap_eq_self hp]; rw [map_comap_eq_self hq]
  simp [sup_le_iff, hp, hq]

中文:
引理 comap_sup_of_injective
  结论: {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂] {p q : 子模 R₂ M₂}
  证明: by
  apply map_injective_of_injective hf
  rw [map_sup]; rw [map_comap_eq_self]; rw [map_comap_eq_self hp]; rw [map_comap_eq_self hq]
  simp [sup_le_iff, hp, hq]

Depends on / 依赖: map_comap_eq_self, map_injective_of_injective, map_sup, sup_le_iff
-/
lemma comap_sup_of_injective {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂] {p q : Submodule R₂ M₂}
    (hf : Function.Injective f) (hp : p <= LinearMap.range f) (hq : q <= LinearMap.range f) :
    comap f (p ⊔ q) = comap f p ⊔ comap f q := by
  apply map_injective_of_injective hf
  rw [map_sup]; rw [map_comap_eq_self]; rw [map_comap_eq_self hp]; rw [map_comap_eq_self hq]
  simp [sup_le_iff, hp, hq]

end AddCommMonoid

section AddCommGroup

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/--
lemma `sup_inf_assoc_of_le_of_neg_le` / 引理 `sup_inf_assoc_of_le_of_neg_le`

English:
lemma sup_inf_assoc_of_le_of_neg_le
  statement: {s : Submodule R M} (t : Submodule R M)
  proof: by
  ext x; simp only [mem_sup, mem_inf]
  constructor
  · rintro ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩
    refine ⟨y, hy, z, ⟨hz, ?_⟩, hyzx⟩
    rw [← add_right_inj]; rw [neg_add_cancel_left] at hyzx
    simpa [hyzx] using p.add_mem (neg_le.mp hnsp hy) hx
  · rintro ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩
    refine ⟨⟨y,

中文:
引理 sup_inf_assoc_of_le_of_neg_le
  结论: {s : 子模 R M} (t : 子模 R M)
  证明: by
  ext x; simp only [mem_sup, mem_inf]
  constructor
  · rintro ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩
    refine ⟨y, hy, z, ⟨hz, ?_⟩, hyzx⟩
    rw [← add_right_inj]; rw [neg_add_cancel_left] at hyzx
    simpa [hyzx] using p.add_mem (neg_le.mp hnsp hy) hx
  · rintro ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩
    refine ⟨⟨y,

Depends on / 依赖: add_mem, add_right_inj, mem_inf, mem_sup, neg_add_cancel_left, neg_le, neg_le.mp, p.add_mem
-/
lemma sup_inf_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M)
    {p : Submodule R M} (hsp : s <= p) (hnsp : -s <= p) :
    (s ⊔ t) ⊓ p = s ⊔ (t ⊓ p) := by
  ext x; simp only [mem_sup, mem_inf]
  constructor
  · rintro ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩
    refine ⟨y, hy, z, ⟨hz, ?_⟩, hyzx⟩
    rw [← add_right_inj]; rw [neg_add_cancel_left] at hyzx
    simpa [hyzx] using p.add_mem (neg_le.mp hnsp hy) hx
  · rintro ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩
    refine ⟨⟨y, hy, z, hz, hyzx⟩, ?_⟩
    simpa [← hyzx] using p.add_mem (hsp hy) hz'

/--
lemma `inf_sup_assoc_of_le_of_neg_le` / 引理 `inf_sup_assoc_of_le_of_neg_le`

English:
lemma inf_sup_assoc_of_le_of_neg_le
  statement: {s : Submodule R M} (t : Submodule R M)
  proof: by
  rw [sup_comm]; rw [inf_comm]; rw [← sup_inf_assoc_of_le_of_neg_le t hps hnps]; rw [inf_comm]; rw [sup_comm]

中文:
引理 inf_sup_assoc_of_le_of_neg_le
  结论: {s : 子模 R M} (t : 子模 R M)
  证明: by
  rw [sup_comm]; rw [inf_comm]; rw [← sup_inf_assoc_of_le_of_neg_le t hps hnps]; rw [inf_comm]; rw [sup_comm]

Depends on / 依赖: inf_comm, sup_comm, sup_inf_assoc_of_le_of_neg_le
-/
lemma inf_sup_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M)
    {p : Submodule R M} (hps : p <= s) (hnps : -p <= s) :
    (s ⊓ t) ⊔ p = s ⊓ (t ⊔ p) := by
  rw [sup_comm]; rw [inf_comm]; rw [← sup_inf_assoc_of_le_of_neg_le t hps hnps]; rw [inf_comm]; rw [sup_comm]

/--
theorem `span_neg_eq_neg` / 定理 `span_neg_eq_neg`

English:
theorem span_neg_eq_neg
  given: (s : Set M)
  statement: span R (-s) = -span R s
  proof: by
  apply le_antisymm
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span

中文:
定理 span_neg_eq_neg
  条件: (s : 集合 M)
  结论: span R (-s) = -span R s
  证明: by
  apply le_antisymm
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span

Depends on / 依赖: Set.neg_subset, coe_set_neg, le_antisymm, neg_le, neg_neg, neg_subset, span_le, subset_span
-/
theorem span_neg_eq_neg (s : Set M) : span R (-s) = -span R s := by
  apply le_antisymm
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/--
lemma `_root_.AddSubgroup.toIntSubmodule_closure` / 引理 `_root_.AddSubgroup.toIntSubmodule_closure`

English:
lemma _root_.AddSubgroup.toIntSubmodule_closure
  given: (s : Set M)
  proof: (Submodule.span_le.mpr AddSubgroup.subset_closure).antisymm'
    ((Submodule.span Int s).toAddSubgroup.closure_le.mpr Submodule.subset_span)

@[simp]

中文:
引理 _root_.加法子群.to整数Submodule_closure
  条件: (s : 集合 M)
  证明: (Submodule.span_le.mpr AddSubgroup.subset_closure).antisymm'
    ((Submodule.span Int s).toAddSubgroup.closure_le.mpr Submodule.subset_span)

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.subset_closure, Submodule, Submodule.span, Submodule.span_le.mpr, Submodule.subset_span, antisymm, closure_le, span_le, subset_closure, subset_span, toAddSubgroup, toAddSubgroup.closure_le.mpr
-/
lemma _root_.AddSubgroup.toIntSubmodule_closure (s : Set M) :
    (AddSubgroup.closure s).toIntSubmodule = .span Int s :=
  (Submodule.span_le.mpr AddSubgroup.subset_closure).antisymm'
    ((Submodule.span Int s).toAddSubgroup.closure_le.mpr Submodule.subset_span)

@[simp]
/--
theorem `span_neg` / 定理 `span_neg`

English:
theorem span_neg
  given: (s : Set M)
  statement: span R (-s) = span R s
  proof: by simp [span_neg_eq_neg]

中文:
定理 span_neg
  条件: (s : 集合 M)
  结论: span R (-s) = span R s
  证明: by simp [span_neg_eq_neg]

Depends on / 依赖: span_neg_eq_neg
-/
theorem span_neg (s : Set M) : span R (-s) = span R s := by simp [span_neg_eq_neg]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsModularLattice (Submodule R M)
  body: ⟨
  fun _ _ hxy _ _ => by rwa [← sup_inf_assoc_of_le_of_neg_le _ hxy (by simpa)]⟩

中文:
实例 :
  签名: 是Modular格 (子模 R M)
  定义体: ⟨
  fun _ _ hxy _ _ => by rwa [← sup_inf_assoc_of_le_of_neg_le _ hxy (by simpa)]⟩
-/
instance : IsModularLattice (Submodule R M) := ⟨
  fun _ _ hxy _ _ => by rwa [← sup_inf_assoc_of_le_of_neg_le _ hxy (by simpa)]⟩

/--
lemma `isCompl_comap_subtype_of_isCompl_of_le` / 引理 `isCompl_comap_subtype_of_isCompl_of_le`

English:
lemma isCompl_comap_subtype_of_isCompl_of_le
  statement: {p q r : Submodule R M}
  proof: by
  simpa [p.mapIic.isCompl_iff, Iic.isCompl_iff] using Iic.isCompl_inf_inf_of_isCompl_of_le h₁ h₂

中文:
引理 isCompl_comap_subtype_of_isCompl_of_le
  结论: {p q r : 子模 R M}
  证明: by
  simpa [p.mapIic.isCompl_iff, Iic.isCompl_iff] using Iic.isCompl_inf_inf_of_isCompl_of_le h₁ h₂

Depends on / 依赖: Iic.isCompl_iff, Iic.isCompl_inf_inf_of_isCompl_of_le, isCompl_iff, isCompl_inf_inf_of_isCompl_of_le, mapIic, p.mapIic.isCompl_iff
-/
lemma isCompl_comap_subtype_of_isCompl_of_le {p q r : Submodule R M}
    (h₁ : IsCompl q r) (h₂ : q <= p) :
    IsCompl (q.comap p.subtype) (r.comap p.subtype) := by
  simpa [p.mapIic.isCompl_iff, Iic.isCompl_iff] using Iic.isCompl_inf_inf_of_isCompl_of_le h₁ h₂

end AddCommGroup

section AddCommGroup

-- TODO: Multiple lemmas in this section should be in earlier files

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]

/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule R M)
  proof: by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩

中文:
定理 comap_map_eq
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (p : 子模 R M)
  证明: by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩

Depends on / 依赖: bot_le, comap_mono, e.symm, le_antisymm, le_comap_map, mem_sup, sub_eq_zero, sup_le
-/
theorem comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    comap f (map f p) = p ⊔ LinearMap.ker f := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩

/--
theorem `map_eq_range_iff` / 定理 `map_eq_range_iff`

English:
theorem map_eq_range_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  proof: by
  simp_rw [le_antisymm_iff, LinearMap.map_le_range, true_and, ← map_top, map_le_iff_le_comap,
    comap_map_eq, codisjoint_iff_le_sup]

中文:
定理 map_eq_range_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R M}
  证明: by
  simp_rw [le_antisymm_iff, LinearMap.map_le_range, true_and, ← map_top, map_le_iff_le_comap,
    comap_map_eq, codisjoint_iff_le_sup]

Depends on / 依赖: LinearMap, LinearMap.map_le_range, codisjoint_iff_le_sup, comap_map_eq, le_antisymm_iff, map_le_iff_le_comap, map_le_range, map_top, simp_rw, true_and
-/
theorem map_eq_range_iff {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    map f p = f.range ↔ Codisjoint p f.ker := by
  simp_rw [le_antisymm_iff, LinearMap.map_le_range, true_and, ← map_top, map_le_iff_le_comap,
    comap_map_eq, codisjoint_iff_le_sup]

/--
theorem `map_lt_map_of_le_of_sup_lt_sup` / 定理 `map_lt_map_of_le_of_sup_lt_sup`

English:
theorem map_lt_map_of_le_of_sup_lt_sup
  statement: {p p' : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} (hab : p <= p')
  proof: by
  simp_rw [← comap_map_eq] at h
  exact lt_of_le_of_ne (map_mono hab) (ne_of_apply_ne _ h.ne)

中文:
定理 map_lt_map_of_le_of_sup_lt_sup
  结论: {p p' : 子模 R M} {f : M ->ₛₗ[τ₁₂] M₂} (hab : p <= p')
  证明: by
  simp_rw [← comap_map_eq] at h
  exact lt_of_le_of_ne (map_mono hab) (ne_of_apply_ne _ h.ne)

Depends on / 依赖: comap_map_eq, h.ne, lt_of_le_of_ne, map_mono, ne_of_apply_ne, simp_rw
-/
theorem map_lt_map_of_le_of_sup_lt_sup {p p' : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} (hab : p <= p')
    (h : p ⊔ LinearMap.ker f < p' ⊔ LinearMap.ker f) : Submodule.map f p < Submodule.map f p' := by
  simp_rw [← comap_map_eq] at h
  exact lt_of_le_of_ne (map_mono hab) (ne_of_apply_ne _ h.ne)

/--
theorem `comap_map_eq_self` / 定理 `comap_map_eq_self`

English:
theorem comap_map_eq_self
  given: {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} (h : LinearMap.ker f <= p)
  proof: by rw [Submodule.comap_map_eq, sup_of_le_left h]

中文:
定理 comap_map_eq_self
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R M} (h : 线性映射.ker f <= p)
  证明: by rw [Submodule.comap_map_eq, sup_of_le_left h]

Depends on / 依赖: Submodule, Submodule.comap_map_eq, comap_map_eq, sup_of_le_left
-/
theorem comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} (h : LinearMap.ker f <= p) :
    comap f (map f p) = p := by rw [Submodule.comap_map_eq, sup_of_le_left h]

/--
theorem `comap_map_sup_of_comap_le` / 定理 `comap_map_sup_of_comap_le`

English:
theorem comap_map_sup_of_comap_le
  statement: {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: by
  refine le_antisymm (fun x h => ?_) (map_le_iff_le_comap.mp le_sup_left)
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, eq⟩ := mem_sup.mp h
  rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [← map_sub] at eq; subst eq
  simpa using p.add_mem (le hz) hy

中文:
定理 comap_map_sup_of_comap_le
  结论: {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: by
  refine le_antisymm (fun x h => ?_) (map_le_iff_le_comap.mp le_sup_left)
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, eq⟩ := mem_sup.mp h
  rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [← map_sub] at eq; subst eq
  simpa using p.add_mem (le hz) hy

Depends on / 依赖: add_comm, add_mem, eq_sub_iff_add_eq, le_antisymm, le_sup_left, map_le_iff_le_comap, map_le_iff_le_comap.mp, map_sub, mem_sup, mem_sup.mp, p.add_mem
-/
theorem comap_map_sup_of_comap_le {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (le : comap f q <= p) : comap f (map f p ⊔ q) = p := by
  refine le_antisymm (fun x h => ?_) (map_le_iff_le_comap.mp le_sup_left)
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, eq⟩ := mem_sup.mp h
  rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [← map_sub] at eq; subst eq
  simpa using p.add_mem (le hz) hy

/--
lemma `disjoint_map_of_ker_le_right` / 引理 `disjoint_map_of_ker_le_right`

English:
lemma disjoint_map_of_ker_le_right
  statement: {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
  proof: by
  rw [disjoint_iff]; rw [map_inf_eq_map_inf_comap]; rw [comap_map_eq]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [sup_eq_left.mpr hker]; rw [hpq.eq_bot]
  exact bot_le

中文:
引理 disjoint_map_of_ker_le_right
  结论: {f : M ->ₛₗ[τ₁₂] M₂} {p q : 子模 R M}
  证明: by
  rw [disjoint_iff]; rw [map_inf_eq_map_inf_comap]; rw [comap_map_eq]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [sup_eq_left.mpr hker]; rw [hpq.eq_bot]
  exact bot_le

Depends on / 依赖: bot_le, comap_bot, comap_map_eq, disjoint_iff, eq_bot, eq_bot_iff, hpq.eq_bot, map_inf_eq_map_inf_comap, map_le_iff_le_comap, sup_eq_left, sup_eq_left.mpr
-/
lemma disjoint_map_of_ker_le_right {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
    (hpq : Disjoint p q) (hker : f.ker <= q) : Disjoint (p.map f) (q.map f) := by
  rw [disjoint_iff]; rw [map_inf_eq_map_inf_comap]; rw [comap_map_eq]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [sup_eq_left.mpr hker]; rw [hpq.eq_bot]
  exact bot_le

/--
lemma `disjoint_map_of_ker_le_left` / 引理 `disjoint_map_of_ker_le_left`

English:
lemma disjoint_map_of_ker_le_left
  statement: {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
  proof: .symm disjoint_map_of_ker_le_right hpq.symm hker

中文:
引理 disjoint_map_of_ker_le_left
  结论: {f : M ->ₛₗ[τ₁₂] M₂} {p q : 子模 R M}
  证明: .symm disjoint_map_of_ker_le_right hpq.symm hker

Depends on / 依赖: disjoint_map_of_ker_le_right, hpq.symm
-/
lemma disjoint_map_of_ker_le_left {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
    (hpq : Disjoint p q) (hker : f.ker <= p) : Disjoint (p.map f) (q.map f) :=
.symm disjoint_map_of_ker_le_right hpq.symm hker

/--
theorem `isCoatom_comap_or_eq_top` / 定理 `isCoatom_comap_or_eq_top`

English:
theorem isCoatom_comap_or_eq_top
  given: (f : M ->ₛₗ[τ₁₂] M₂) {p : Submodule R₂ M₂} (hp : IsCoatom p)
  proof: or_iff_not_imp_right.mpr fun h => ⟨h, fun q lt => by
    rw [← comap_map_sup_of_comap_le lt.le]; rw [hp.2 (map f q ⊔ p)]; rw [comap_top]
    simpa only [right_lt_sup, map_le_iff_le_comap] using lt.not_ge⟩

中文:
定理 isCoatom_comap_or_eq_top
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {p : 子模 R₂ M₂} (hp : IsCoatom p)
  证明: or_iff_not_imp_right.mpr fun h => ⟨h, fun q lt => by
    rw [← comap_map_sup_of_comap_le lt.le]; rw [hp.2 (map f q ⊔ p)]; rw [comap_top]
    simpa only [right_lt_sup, map_le_iff_le_comap] using lt.not_ge⟩

Depends on / 依赖: comap_map_sup_of_comap_le, comap_top, lt.le, lt.not_ge, map_le_iff_le_comap, not_ge, or_iff_not_imp_right, or_iff_not_imp_right.mpr, right_lt_sup
-/
theorem isCoatom_comap_or_eq_top (f : M ->ₛₗ[τ₁₂] M₂) {p : Submodule R₂ M₂} (hp : IsCoatom p) :
    IsCoatom (comap f p) ∨ comap f p = ⊤ :=
  or_iff_not_imp_right.mpr fun h => ⟨h, fun q lt => by
    rw [← comap_map_sup_of_comap_le lt.le]; rw [hp.2 (map f q ⊔ p)]; rw [comap_top]
    simpa only [right_lt_sup, map_le_iff_le_comap] using lt.not_ge⟩

/--
theorem `isCoatom_comap_iff` / 定理 `isCoatom_comap_iff`

English:
theorem isCoatom_comap_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R₂ M₂}
  proof: by
  have := comap_injective_of_surjective hf
  rw [IsCoatom]; rw [IsCoatom]; rw [← comap_top f]; rw [this.ne_iff]
  refine and_congr_right fun _ =>
    ⟨fun h m hm => this (h _ <| comap_strictMono_of_surjective hf hm), fun h m hm => ?_⟩
  rw [← h _ (lt_map_of_comap_lt_of_surjective hf hm)]; rw [com

中文:
定理 isCoatom_comap_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : 满射 f) {p : 子模 R₂ M₂}
  证明: by
  have := comap_injective_of_surjective hf
  rw [IsCoatom]; rw [IsCoatom]; rw [← comap_top f]; rw [this.ne_iff]
  refine and_congr_right fun _ =>
    ⟨fun h m hm => this (h _ <| comap_strictMono_of_surjective hf hm), fun h m hm => ?_⟩
  rw [← h _ (lt_map_of_comap_lt_of_surjective hf hm)]; rw [com

Depends on / 依赖: IsCoatom, and_congr_right, bot_le, comap_injective_of_surjective, comap_map_eq_self, comap_mono, comap_strictMono_of_surjective, comap_top, hm.le, lt_map_of_comap_lt_of_surjective, ne_iff, this.ne_iff
-/
theorem isCoatom_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R₂ M₂} :
    IsCoatom (comap f p) ↔ IsCoatom p := by
  have := comap_injective_of_surjective hf
  rw [IsCoatom]; rw [IsCoatom]; rw [← comap_top f]; rw [this.ne_iff]
  refine and_congr_right fun _ =>
    ⟨fun h m hm => this (h _ <| comap_strictMono_of_surjective hf hm), fun h m hm => ?_⟩
  rw [← h _ (lt_map_of_comap_lt_of_surjective hf hm)]; rw [comap_map_eq_self ((comap_mono bot_le).trans hm.le)]

/--
theorem `isCoatom_map_of_ker_le` / 定理 `isCoatom_map_of_ker_le`

English:
theorem isCoatom_map_of_ker_le
  statement: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R M}
  proof: (isCoatom_comap_iff hf).mp by rwa [comap_map_eq_self le]

中文:
定理 isCoatom_map_of_ker_le
  结论: {f : M ->ₛₗ[τ₁₂] M₂} (hf : 满射 f) {p : 子模 R M}
  证明: (isCoatom_comap_iff hf).mp by rwa [comap_map_eq_self le]

Depends on / 依赖: comap_map_eq_self, isCoatom_comap_iff
-/
theorem isCoatom_map_of_ker_le {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R M}
    (le : LinearMap.ker f <= p) (hp : IsCoatom p) : IsCoatom (map f p) :=
(isCoatom_comap_iff hf).mp by rwa [comap_map_eq_self le]

/--
theorem `map_iInf_of_ker_le` / 定理 `map_iInf_of_ker_le`

English:
theorem map_iInf_of_ker_le
  statement: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {ι} {p : ι -> Submodule R M}
  proof: by
  conv_rhs => rw [← map_comap_eq_of_surjective hf (⨅ _, _), comap_iInf]
  simp_rw [fun i => comap_map_eq_self (le_iInf_iff.mp h i)]

中文:
定理 map_iInf_of_ker_le
  结论: {f : M ->ₛₗ[τ₁₂] M₂} (hf : 满射 f) {ι} {p : ι -> 子模 R M}
  证明: by
  conv_rhs => rw [← map_comap_eq_of_surjective hf (⨅ _, _), comap_iInf]
  simp_rw [fun i => comap_map_eq_self (le_iInf_iff.mp h i)]

Depends on / 依赖: comap_iInf, comap_map_eq_self, conv_rhs, le_iInf_iff, le_iInf_iff.mp, map_comap_eq_of_surjective, simp_rw
-/
theorem map_iInf_of_ker_le {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {ι} {p : ι -> Submodule R M}
    (h : LinearMap.ker f <= ⨅ i, p i) : map f (⨅ i, p i) = ⨅ i, map f (p i) := by
  conv_rhs => rw [← map_comap_eq_of_surjective hf (⨅ _, _), comap_iInf]
  simp_rw [fun i => comap_map_eq_self (le_iInf_iff.mp h i)]

/--
lemma `comap_covBy_of_surjective` / 引理 `comap_covBy_of_surjective`

English:
lemma comap_covBy_of_surjective
  statement: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f)
  proof: by
  refine ⟨lt_of_le_of_ne (comap_mono h.1.le) ((comap_injective_of_surjective hf).ne h.1.ne), ?_⟩
  intro N h₁ h₂
  refine h.2 (lt_map_of_comap_lt_of_surjective hf h₁) ?_
  rwa [← comap_lt_comap_iff_of_surjective hf, comap_map_eq, sup_eq_left.mpr]
  refine (LinearMap.ker_le_comap (f : M ->ₛₗ[τ₁₂] 

中文:
引理 comap_covBy_of_surjective
  结论: {f : M ->ₛₗ[τ₁₂] M₂} (hf : 满射 f)
  证明: by
  refine ⟨lt_of_le_of_ne (comap_mono h.1.le) ((comap_injective_of_surjective hf).ne h.1.ne), ?_⟩
  intro N h₁ h₂
  refine h.2 (lt_map_of_comap_lt_of_surjective hf h₁) ?_
  rwa [← comap_lt_comap_iff_of_surjective hf, comap_map_eq, sup_eq_left.mpr]
  refine (LinearMap.ker_le_comap (f : M ->ₛₗ[τ₁₂] 

Depends on / 依赖: LinearMap, LinearMap.ker_le_comap, comap_injective_of_surjective, comap_lt_comap_iff_of_surjective, comap_map_eq, comap_mono, ker_le_comap, lt_map_of_comap_lt_of_surjective, lt_of_le_of_ne, sup_eq_left, sup_eq_left.mpr
-/
lemma comap_covBy_of_surjective {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f)
    {p q : Submodule R₂ M₂} (h : p ⋖ q) :
    p.comap f ⋖ q.comap f := by
  refine ⟨lt_of_le_of_ne (comap_mono h.1.le) ((comap_injective_of_surjective hf).ne h.1.ne), ?_⟩
  intro N h₁ h₂
  refine h.2 (lt_map_of_comap_lt_of_surjective hf h₁) ?_
  rwa [← comap_lt_comap_iff_of_surjective hf, comap_map_eq, sup_eq_left.mpr]
  refine (LinearMap.ker_le_comap (f : M ->ₛₗ[τ₁₂] M₂)).trans h₁.le

@[deprecated map_eq_range_iff (since := "2026-07-01")]
/--
lemma `_root_.LinearMap.range_domRestrict_eq_range_iff` / 引理 `_root_.LinearMap.range_domRestrict_eq_range_iff`

English:
lemma _root_.LinearMap.range_domRestrict_eq_range_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M}
  proof: by
  simp [map_eq_range_iff]

中文:
引理 _root_.线性映射.range_domRestrict_eq_range_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {S : 子模 R M}
  证明: by
  simp [map_eq_range_iff]

Depends on / 依赖: map_eq_range_iff
-/
lemma _root_.LinearMap.range_domRestrict_eq_range_iff {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    LinearMap.range (f.domRestrict S) = LinearMap.range f ↔ Codisjoint S f.ker := by
  simp [map_eq_range_iff]

/--
lemma `_root_.LinearMap.surjective_domRestrict_iff` / 引理 `_root_.LinearMap.surjective_domRestrict_iff`

English:
lemma _root_.LinearMap.surjective_domRestrict_iff
  proof: by
  rw [← LinearMap.range_eq_top] at hf ⊢
  rw [← hf]; rw [LinearMap.range_domRestrict]; rw [map_eq_range_iff]

中文:
引理 _root_.线性映射.surjective_domRestrict_iff
  证明: by
  rw [← LinearMap.range_eq_top] at hf ⊢
  rw [← hf]; rw [LinearMap.range_domRestrict]; rw [map_eq_range_iff]
-/
@[simp] lemma _root_.LinearMap.surjective_domRestrict_iff
    {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M} (hf : Surjective f) :
    Surjective (f.domRestrict S) ↔ Codisjoint S f.ker := by
  rw [← LinearMap.range_eq_top] at hf ⊢
  rw [← hf]; rw [LinearMap.range_domRestrict]; rw [map_eq_range_iff]

/--
lemma `biSup_comap_eq_top_of_surjective` / 引理 `biSup_comap_eq_top_of_surjective`

English:
lemma biSup_comap_eq_top_of_surjective
  statement: {ι : Type*} (s : Set ι) (hs : s.Nonempty)
  proof: by
  obtain ⟨k, hk⟩ := hs
  suffices (⨆ i in s, (p i).comap f) ⊔ LinearMap.ker f = ⊤ by
    rw [← this]; rw [left_eq_sup]; exact le_trans f.ker_le_comap (le_biSup (fun i => (p i).comap f) hk)
  rw [iSup_subtype'] at hp ⊢
  rw [← comap_map_eq]; rw [map_iSup_comap_of_surjective hf]; rw [hp]; rw [comap

中文:
引理 biSup_comap_eq_top_of_surjective
  结论: {ι : 类型} (s : 集合 ι) (hs : s.非空)
  证明: by
  obtain ⟨k, hk⟩ := hs
  suffices (⨆ i in s, (p i).comap f) ⊔ LinearMap.ker f = ⊤ by
    rw [← this]; rw [left_eq_sup]; exact le_trans f.ker_le_comap (le_biSup (fun i => (p i).comap f) hk)
  rw [iSup_subtype'] at hp ⊢
  rw [← comap_map_eq]; rw [map_iSup_comap_of_surjective hf]; rw [hp]; rw [comap

Depends on / 依赖: LinearMap, LinearMap.ker, comap_map_eq, comap_top, f.ker_le_comap, iSup_subtype, ker_le_comap, le_biSup, le_trans, left_eq_sup, map_iSup_comap_of_surjective
-/
lemma biSup_comap_eq_top_of_surjective {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι -> Submodule R₂ M₂) (hp : ⨆ i in s, p i = ⊤)
    (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) :
    ⨆ i in s, (p i).comap f = ⊤ := by
  obtain ⟨k, hk⟩ := hs
  suffices (⨆ i in s, (p i).comap f) ⊔ LinearMap.ker f = ⊤ by
    rw [← this]; rw [left_eq_sup]; exact le_trans f.ker_le_comap (le_biSup (fun i => (p i).comap f) hk)
  rw [iSup_subtype'] at hp ⊢
  rw [← comap_map_eq]; rw [map_iSup_comap_of_surjective hf]; rw [hp]; rw [comap_top]

/--
lemma `biSup_comap_eq_top_of_range_eq_biSup` / 引理 `biSup_comap_eq_top_of_range_eq_biSup`

English:
lemma biSup_comap_eq_top_of_range_eq_biSup
  proof: by
  suffices ⨆ i in s, (p i).comap (LinearMap.range f).subtype = ⊤ by
    rw [← biSup_comap_eq_top_of_surjective s hs _ this _ f.surjective_rangeRestrict]; rfl
  exact hf ▸ biSup_comap_subtype_eq_top s p

中文:
引理 biSup_comap_eq_top_of_range_eq_biSup
  证明: by
  suffices ⨆ i in s, (p i).comap (LinearMap.range f).subtype = ⊤ by
    rw [← biSup_comap_eq_top_of_surjective s hs _ this _ f.surjective_rangeRestrict]; rfl
  exact hf ▸ biSup_comap_subtype_eq_top s p

Depends on / 依赖: LinearMap, LinearMap.range, biSup_comap_eq_top_of_surjective, biSup_comap_subtype_eq_top, f.surjective_rangeRestrict, subtype, surjective_rangeRestrict
-/
lemma biSup_comap_eq_top_of_range_eq_biSup
    {R R₂ : Type*} [Semiring R] [Ring R₂] {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]
    [Module R M] [Module R₂ M₂] {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι -> Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂) (hf : LinearMap.range f = ⨆ i in s, p i) :
    ⨆ i in s, (p i).comap f = ⊤ := by
  suffices ⨆ i in s, (p i).comap (LinearMap.range f).subtype = ⊤ by
    rw [← biSup_comap_eq_top_of_surjective s hs _ this _ f.surjective_rangeRestrict]; rfl
  exact hf ▸ biSup_comap_subtype_eq_top s p

end AddCommGroup

section Ring

variable [Ring R] [Semiring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]
variable {p p' : Submodule R M}

/--
theorem `map_strict_mono_or_ker_sup_lt_ker_sup` / 定理 `map_strict_mono_or_ker_sup_lt_ker_sup`

English:
theorem map_strict_mono_or_ker_sup_lt_ker_sup
  given: (f : M ->ₛₗ[τ₁₂] M₂) (hab : p < p')
  proof: by
obtain (⟨h, -⟩ | ⟨-, h⟩) := Prod.mk_lt_mk.mp strictMono_inf_prod_sup (z := LinearMap.ker f) hab
  · simpa [inf_comm] using Or.inr h
· apply Or.inl map_lt_map_of_le_of_sup_lt_sup hab.le h

中文:
定理 map_strict_mono_or_ker_sup_lt_ker_sup
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (hab : p < p')
  证明: by
obtain (⟨h, -⟩ | ⟨-, h⟩) := Prod.mk_lt_mk.mp strictMono_inf_prod_sup (z := LinearMap.ker f) hab
  · simpa [inf_comm] using Or.inr h
· apply Or.inl map_lt_map_of_le_of_sup_lt_sup hab.le h

Depends on / 依赖: LinearMap, LinearMap.ker, Or.inl, Or.inr, Prod.mk_lt_mk.mp, hab.le, inf_comm, map_lt_map_of_le_of_sup_lt_sup, mk_lt_mk, strictMono_inf_prod_sup
-/
theorem map_strict_mono_or_ker_sup_lt_ker_sup (f : M ->ₛₗ[τ₁₂] M₂) (hab : p < p') :
    Submodule.map f p < Submodule.map f p' ∨ LinearMap.ker f ⊓ p < LinearMap.ker f ⊓ p' := by
obtain (⟨h, -⟩ | ⟨-, h⟩) := Prod.mk_lt_mk.mp strictMono_inf_prod_sup (z := LinearMap.ker f) hab
  · simpa [inf_comm] using Or.inr h
· apply Or.inl map_lt_map_of_le_of_sup_lt_sup hab.le h

/--
theorem `_root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt` / 定理 `_root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt`

English:
theorem _root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt
  statement: {f : M ->ₛₗ[τ₁₂] M₂}
  proof: .resolve_left q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

中文:
定理 _root_.线性映射.ker_inf_lt_ker_inf_of_map_eq_of_lt
  结论: {f : M ->ₛₗ[τ₁₂] M₂}
  证明: .resolve_left q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

Depends on / 依赖: map_strict_mono_or_ker_sup_lt_ker_sup, not_lt, q.not_lt, resolve_left
-/
theorem _root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt {f : M ->ₛₗ[τ₁₂] M₂}
    (hab : p < p') (q : Submodule.map f p = Submodule.map f p') :
    LinearMap.ker f ⊓ p < LinearMap.ker f ⊓ p' :=
.resolve_left q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

/--
theorem `map_strict_mono_of_ker_inf_eq` / 定理 `map_strict_mono_of_ker_inf_eq`

English:
theorem map_strict_mono_of_ker_inf_eq
  statement: {f : M ->ₛₗ[τ₁₂] M₂} (hab : p < p')
  proof: .resolve_right q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

中文:
定理 map_strict_mono_of_ker_inf_eq
  结论: {f : M ->ₛₗ[τ₁₂] M₂} (hab : p < p')
  证明: .resolve_right q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

Depends on / 依赖: map_strict_mono_or_ker_sup_lt_ker_sup, not_lt, q.not_lt, resolve_right
-/
theorem map_strict_mono_of_ker_inf_eq {f : M ->ₛₗ[τ₁₂] M₂} (hab : p < p')
    (q : LinearMap.ker f ⊓ p = LinearMap.ker f ⊓ p') : Submodule.map f p < Submodule.map f p' :=
.resolve_right q.not_lt map_strict_mono_or_ker_sup_lt_ker_sup f hab

/--
lemma `disjoint_span_singleton''` / 引理 `disjoint_span_singleton''`

English:
lemma disjoint_span_singleton''
  given: {s : Submodule R M} {x : M}
  proof: by
  rw [disjoint_comm]; simp +contextual [disjoint_def, mem_span_singleton]

中文:
引理 disjoint_span_singleton''
  条件: {s : 子模 R M} {x : M}
  证明: by
  rw [disjoint_comm]; simp +contextual [disjoint_def, mem_span_singleton]

Depends on / 依赖: contextual, disjoint_comm, disjoint_def, mem_span_singleton
-/
lemma disjoint_span_singleton'' {s : Submodule R M} {x : M} :
    Disjoint s (R ∙ x) ↔ forall r : R, r • x in s -> r • x = 0 := by
  rw [disjoint_comm]; simp +contextual [disjoint_def, mem_span_singleton]

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {s : Submodule K V} {x : V}

/--
theorem `wcovBy_span_singleton_sup` / 定理 `wcovBy_span_singleton_sup`

English:
theorem wcovBy_span_singleton_sup
  given: (x : V) (s : Submodule K V)
  statement: WCovBy s (K ∙ x ⊔ s)
  proof: by
  refine ⟨le_sup_right, fun q hpq hqp => hqp.not_ge ?_⟩
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  obtain ⟨c, z, hz, rfl⟩ : exists c : K, exists z in s, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hz] at hy

中文:
定理 wcovBy_span_singleton_sup
  条件: (x : V) (s : 子模 K V)
  结论: WCovBy s (K ∙ x ⊔ s)
  证明: by
  refine ⟨le_sup_right, fun q hpq hqp => hqp.not_ge ?_⟩
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  obtain ⟨c, z, hz, rfl⟩ : exists c : K, exists z in s, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hz] at hy

Depends on / 依赖: SetLike, SetLike.exists_of_lt, add_mem_iff_left, eq_or_ne, exists_of_lt, hpq.le, hqp.le, hqp.not_ge, le_sup_right, mem_span_singleton, mem_sup, not_ge, q.add_mem_iff_left, q.smul_mem_iff, smul_mem_iff
-/
theorem wcovBy_span_singleton_sup (x : V) (s : Submodule K V) : WCovBy s (K ∙ x ⊔ s) := by
  refine ⟨le_sup_right, fun q hpq hqp => hqp.not_ge ?_⟩
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  obtain ⟨c, z, hz, rfl⟩ : exists c : K, exists z in s, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hz] at hyp
  · have : x in q := by
      rwa [q.add_mem_iff_left (hpq.le hz), q.smul_mem_iff hc] at hyq
    simp [hpq.le, this]

/--
theorem `covBy_span_singleton_sup` / 定理 `covBy_span_singleton_sup`

English:
theorem covBy_span_singleton_sup
  given: {x : V} {s : Submodule K V} (h : x ∉ s)
  statement: CovBy s (K ∙ x ⊔ s)
  proof: ⟨by simpa, (wcovBy_span_singleton_sup _ _).2⟩

中文:
定理 covBy_span_singleton_sup
  条件: {x : V} {s : 子模 K V} (h : x ∉ s)
  结论: CovBy s (K ∙ x ⊔ s)
  证明: ⟨by simpa, (wcovBy_span_singleton_sup _ _).2⟩

Depends on / 依赖: wcovBy_span_singleton_sup
-/
theorem covBy_span_singleton_sup {x : V} {s : Submodule K V} (h : x ∉ s) : CovBy s (K ∙ x ⊔ s) :=
  ⟨by simpa, (wcovBy_span_singleton_sup _ _).2⟩

/--
theorem `disjoint_span_singleton` / 定理 `disjoint_span_singleton`

English:
theorem disjoint_span_singleton
  statement: Disjoint s (K ∙ x) ↔ x in s -> x = 0
  proof: by
  simpa +contextual [disjoint_span_singleton'', or_iff_not_imp_left, forall_comm (β := ¬_),
    s.smul_mem_iff] using ⟨fun h => h _ one_ne_zero, fun h _ _ => h⟩

中文:
定理 disjoint_span_singleton
  结论: Disjoint s (K ∙ x) ↔ x in s -> x = 0
  证明: by
  simpa +contextual [disjoint_span_singleton'', or_iff_not_imp_left, forall_comm (β := ¬_),
    s.smul_mem_iff] using ⟨fun h => h _ one_ne_zero, fun h _ _ => h⟩

Depends on / 依赖: contextual, disjoint_span_singleton, forall_comm, one_ne_zero, or_iff_not_imp_left, s.smul_mem_iff, smul_mem_iff
-/
theorem disjoint_span_singleton : Disjoint s (K ∙ x) ↔ x in s -> x = 0 := by
  simpa +contextual [disjoint_span_singleton'', or_iff_not_imp_left, forall_comm (β := ¬_),
    s.smul_mem_iff] using ⟨fun h => h _ one_ne_zero, fun h _ _ => h⟩

/--
theorem `disjoint_span_singleton'` / 定理 `disjoint_span_singleton'`

English:
theorem disjoint_span_singleton'
  given: (hx : x != 0)
  statement: Disjoint s (K ∙ x) ↔ x ∉ s
  proof: by
  simp [disjoint_span_singleton, hx]

中文:
定理 disjoint_span_singleton'
  条件: (hx : x != 0)
  结论: Disjoint s (K ∙ x) ↔ x ∉ s
  证明: by
  simp [disjoint_span_singleton, hx]

Depends on / 依赖: disjoint_span_singleton
-/
theorem disjoint_span_singleton' (hx : x != 0) : Disjoint s (K ∙ x) ↔ x ∉ s := by
  simp [disjoint_span_singleton, hx]

/--
lemma `disjoint_span_singleton_of_notMem` / 引理 `disjoint_span_singleton_of_notMem`

English:
lemma disjoint_span_singleton_of_notMem
  given: (hx : x ∉ s)
  statement: Disjoint s (K ∙ x)
  proof: by
  simp [disjoint_span_singleton, hx]

中文:
引理 disjoint_span_singleton_of_notMem
  条件: (hx : x ∉ s)
  结论: Disjoint s (K ∙ x)
  证明: by
  simp [disjoint_span_singleton, hx]

Depends on / 依赖: disjoint_span_singleton
-/
lemma disjoint_span_singleton_of_notMem (hx : x ∉ s) : Disjoint s (K ∙ x) := by
  simp [disjoint_span_singleton, hx]

/--
lemma `isCompl_span_singleton_of_isCoatom_of_notMem` / 引理 `isCompl_span_singleton_of_isCoatom_of_notMem`

English:
lemma isCompl_span_singleton_of_isCoatom_of_notMem
  given: (hs : IsCoatom s) (hx : x ∉ s)
  proof: by
  refine ⟨disjoint_span_singleton_of_notMem hx, ?_⟩
  rw [← covBy_top_iff] at hs
  simpa only [codisjoint_iff, sup_comm, not_lt_top_iff] using hs.2 (covBy_span_singleton_sup hx).1

中文:
引理 isCompl_span_singleton_of_isCoatom_of_notMem
  条件: (hs : IsCoatom s) (hx : x ∉ s)
  证明: by
  refine ⟨disjoint_span_singleton_of_notMem hx, ?_⟩
  rw [← covBy_top_iff] at hs
  simpa only [codisjoint_iff, sup_comm, not_lt_top_iff] using hs.2 (covBy_span_singleton_sup hx).1

Depends on / 依赖: codisjoint_iff, covBy_span_singleton_sup, covBy_top_iff, disjoint_span_singleton_of_notMem, not_lt_top_iff, sup_comm
-/
lemma isCompl_span_singleton_of_isCoatom_of_notMem (hs : IsCoatom s) (hx : x ∉ s) :
    IsCompl s (K ∙ x) := by
  refine ⟨disjoint_span_singleton_of_notMem hx, ?_⟩
  rw [← covBy_top_iff] at hs
  simpa only [codisjoint_iff, sup_comm, not_lt_top_iff] using hs.2 (covBy_span_singleton_sup hx).1

end DivisionRing

end Submodule

namespace LinearMap

open Submodule Function

section AddCommGroup

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]

/--
theorem `map_le_map_iff` / 定理 `map_le_map_iff`

English:
theorem map_le_map_iff
  given: (f : M ->ₛₗ[τ₁₂] M₂) {p p'}
  proof: by
  rw [map_le_iff_le_comap]; rw [Submodule.comap_map_eq]

中文:
定理 map_le_map_iff
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {p p'}
  证明: by
  rw [map_le_iff_le_comap]; rw [Submodule.comap_map_eq]
-/
protected theorem map_le_map_iff (f : M ->ₛₗ[τ₁₂] M₂) {p p'} :
    map f p <= map f p' ↔ p <= p' ⊔ ker f := by
  rw [map_le_iff_le_comap]; rw [Submodule.comap_map_eq]

/--
theorem `map_le_map_iff'` / 定理 `map_le_map_iff'`

English:
theorem map_le_map_iff'
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'}
  proof: by
  rw [LinearMap.map_le_map_iff]; rw [hf]; rw [sup_bot_eq]

中文:
定理 map_le_map_iff'
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'}
  证明: by
  rw [LinearMap.map_le_map_iff]; rw [hf]; rw [sup_bot_eq]

Depends on / 依赖: LinearMap, LinearMap.map_le_map_iff, map_le_map_iff, sup_bot_eq
-/
theorem map_le_map_iff' {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'} :
    map f p <= map f p' ↔ p <= p' := by
  rw [LinearMap.map_le_map_iff]; rw [hf]; rw [sup_bot_eq]

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥)
  statement: Injective (map f)
  proof: fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

中文:
定理 map_injective
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥)
  结论: 单射 (map f)
  证明: fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))
-/
theorem map_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) : Injective (map f) := fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

/--
theorem `map_eq_top_iff` / 定理 `map_eq_top_iff`

English:
theorem map_eq_top_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : Submodule R M}
  proof: by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

中文:
定理 map_eq_top_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : 子模 R M}
  证明: by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

Depends on / 依赖: LinearMap, LinearMap.map_le_map_iff, map_le_map_iff, range_eq_map, simp_rw, top_le_iff
-/
theorem map_eq_top_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : Submodule R M} :
    p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤ := by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

end AddCommGroup

section

variable (R) (M) [Semiring R] [AddCommMonoid M] [Module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
`R` to scalar multiples of `x`. See also `LinearMap.ringLmapEquivSelf`. -/
@[simps!]
/--
Definition of `toSpanSingleton` / `toSpanSingleton` 的定义

English:
definition toSpanSingleton
  signature: (x : M)
  body: LinearMap.id.smulRight x

中文:
定义 toSpanSingleton
  签名: (x : M)
  定义体: LinearMap.id.smulRight x

Depends on / 依赖: LinearMap, LinearMap.id.smulRight, smulRight
-/
def toSpanSingleton (x : M) : R ->ₗ[R] M :=
  LinearMap.id.smulRight x

/--
lemma `smulRight_id` / 引理 `smulRight_id`

English:
lemma smulRight_id
  statement: id.smulRight = toSpanSingleton R M
  proof: rfl

中文:
引理 smulRight_id
  结论: id.smulRight = toSpanSingleton R M
  证明: rfl
-/
lemma smulRight_id : id.smulRight = toSpanSingleton R M := rfl

/--
theorem `toSpanSingleton_apply_one` / 定理 `toSpanSingleton_apply_one`

English:
theorem toSpanSingleton_apply_one
  given: (x : M)
  statement: toSpanSingleton R M x 1 = x
  proof: one_smul _ _

中文:
定理 toSpanSingleton_apply_one
  条件: (x : M)
  结论: toSpanSingleton R M x 1 = x
  证明: one_smul _ _

Depends on / 依赖: one_smul
-/
theorem toSpanSingleton_apply_one (x : M) : toSpanSingleton R M x 1 = x :=
  one_smul _ _

/--
theorem `toSpanSingleton_injective` / 定理 `toSpanSingleton_injective`

English:
theorem toSpanSingleton_injective
  statement: Function.Injective (toSpanSingleton R M)
  proof: fun _ _ eq => by simpa using congr($eq 1)

@[simp]

中文:
定理 toSpanSingleton_injective
  结论: 函数.单射 (toSpanSingleton R M)
  证明: fun _ _ eq => by simpa using congr($eq 1)

@[simp]
-/
theorem toSpanSingleton_injective : Function.Injective (toSpanSingleton R M) :=
  fun _ _ eq => by simpa using congr($eq 1)

@[simp]
/--
theorem `toSpanSingleton_zero` / 定理 `toSpanSingleton_zero`

English:
theorem toSpanSingleton_zero
  statement: toSpanSingleton R M 0 = 0
  proof: by
  ext
  simp

中文:
定理 toSpanSingleton_zero
  结论: toSpanSingleton R M 0 = 0
  证明: by
  ext
  simp
-/
theorem toSpanSingleton_zero : toSpanSingleton R M 0 = 0 := by
  ext
  simp

/--
theorem `toSpanSingleton_eq_zero_iff` / 定理 `toSpanSingleton_eq_zero_iff`

English:
theorem toSpanSingleton_eq_zero_iff
  given: {x : M}
  statement: toSpanSingleton R M x = 0 ↔ x = 0
  proof: by
  rw [← toSpanSingleton_zero]; rw [(toSpanSingleton_injective R M).eq_iff]

中文:
定理 toSpanSingleton_eq_zero_iff
  条件: {x : M}
  结论: toSpanSingleton R M x = 0 ↔ x = 0
  证明: by
  rw [← toSpanSingleton_zero]; rw [(toSpanSingleton_injective R M).eq_iff]

Depends on / 依赖: eq_iff, toSpanSingleton_injective, toSpanSingleton_zero
-/
theorem toSpanSingleton_eq_zero_iff {x : M} : toSpanSingleton R M x = 0 ↔ x = 0 := by
  rw [← toSpanSingleton_zero]; rw [(toSpanSingleton_injective R M).eq_iff]

variable {R M}

/--
lemma `toSpanSingleton_add` / 引理 `toSpanSingleton_add`

English:
lemma toSpanSingleton_add
  given: (x y : M)
  proof: by
  ext; simp

中文:
引理 toSpanSingleton_add
  条件: (x y : M)
  证明: by
  ext; simp
-/
lemma toSpanSingleton_add (x y : M) :
    toSpanSingleton R M (x + y) = toSpanSingleton R M x + toSpanSingleton R M y := by
  ext; simp

/--
theorem `toSpanSingleton_smul` / 定理 `toSpanSingleton_smul`

English:
theorem toSpanSingleton_smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S M]
  proof: by
  ext; simp

中文:
定理 toSpanSingleton_smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S M]
  证明: by
  ext; simp
-/
theorem toSpanSingleton_smul {S : Type*} [Monoid S] [DistribMulAction S M]
    [SMulCommClass R S M] (r : S) (x : M) :
    toSpanSingleton R M (r • x) = r • toSpanSingleton R M x := by
  ext; simp

/--
theorem `toSpanSingleton_isIdempotentElem_iff` / 定理 `toSpanSingleton_isIdempotentElem_iff`

English:
theorem toSpanSingleton_isIdempotentElem_iff
  given: {e : R}
  proof: by
  simp_rw [IsIdempotentElem, LinearMap.ext_iff, Module.End.mul_apply, toSpanSingleton_apply,
    smul_eq_mul, mul_assoc]
  exact ⟨fun h => by conv_rhs => rw [← one_mul e, ← h, one_mul], fun h _ => by rw [h]⟩

中文:
定理 toSpanSingleton_isIdempotentElem_iff
  条件: {e : R}
  证明: by
  simp_rw [IsIdempotentElem, LinearMap.ext_iff, Module.End.mul_apply, toSpanSingleton_apply,
    smul_eq_mul, mul_assoc]
  exact ⟨fun h => by conv_rhs => rw [← one_mul e, ← h, one_mul], fun h _ => by rw [h]⟩

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.ext_iff, Module, Module.End.mul_apply, conv_rhs, ext_iff, mul_apply, mul_assoc, one_mul, simp_rw, smul_eq_mul, toSpanSingleton_apply
-/
theorem toSpanSingleton_isIdempotentElem_iff {e : R} :
    IsIdempotentElem (toSpanSingleton R R e) ↔ IsIdempotentElem e := by
  simp_rw [IsIdempotentElem, LinearMap.ext_iff, Module.End.mul_apply, toSpanSingleton_apply,
    smul_eq_mul, mul_assoc]
  exact ⟨fun h => by conv_rhs => rw [← one_mul e, ← h, one_mul], fun h _ => by rw [h]⟩

/--
theorem `isIdempotentElem_map_one_iff` / 定理 `isIdempotentElem_map_one_iff`

English:
theorem isIdempotentElem_map_one_iff
  given: {f : Module.End R R}
  proof: by
  rw [IsIdempotentElem]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [IsIdempotentElem]; rw [LinearMap.ext_iff]
  simp_rw [Module.End.mul_apply]
  exact ⟨fun h r => by rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, h], (· 1)⟩

中文:
定理 isIdempotentElem_map_one_iff
  条件: {f : 模.End R R}
  证明: by
  rw [IsIdempotentElem]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [IsIdempotentElem]; rw [LinearMap.ext_iff]
  simp_rw [Module.End.mul_apply]
  exact ⟨fun h r => by rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, h], (· 1)⟩

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.ext_iff, Module, Module.End.mul_apply, ext_iff, map_smul, mul_apply, mul_one, simp_rw, smul_eq_mul
-/
theorem isIdempotentElem_map_one_iff {f : Module.End R R} :
    IsIdempotentElem (f 1) ↔ IsIdempotentElem f := by
  rw [IsIdempotentElem]; rw [← smul_eq_mul]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [IsIdempotentElem]; rw [LinearMap.ext_iff]
  simp_rw [Module.End.mul_apply]
  exact ⟨fun h r => by rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, h], (· 1)⟩

/--
theorem `range_toSpanSingleton` / 定理 `range_toSpanSingleton`

English:
theorem range_toSpanSingleton
  given: (x : M)
  proof: SetLike.coe_injective (Submodule.span_singleton_eq_range R x).symm

中文:
定理 range_toSpanSingleton
  条件: (x : M)
  证明: SetLike.coe_injective (Submodule.span_singleton_eq_range R x).symm

Depends on / 依赖: SetLike, SetLike.coe_injective, Submodule, Submodule.span_singleton_eq_range, coe_injective, span_singleton_eq_range
-/
theorem range_toSpanSingleton (x : M) :
    range (toSpanSingleton R M x) = .span R {x} :=
  SetLike.coe_injective (Submodule.span_singleton_eq_range R x).symm

variable (R M) in
/--
theorem `span_singleton_eq_range` / 定理 `span_singleton_eq_range`

English:
theorem span_singleton_eq_range
  given: (x : M)
  proof: .symm range_toSpanSingleton x

中文:
定理 span_singleton_eq_range
  条件: (x : M)
  证明: .symm range_toSpanSingleton x

Depends on / 依赖: range_toSpanSingleton
-/
theorem span_singleton_eq_range (x : M) :
    R ∙ x = range (toSpanSingleton R M x) :=
.symm range_toSpanSingleton x

/--
theorem `comp_toSpanSingleton` / 定理 `comp_toSpanSingleton`

English:
theorem comp_toSpanSingleton
  given: [AddCommMonoid M₂] [Module R M₂] (f : M ->ₗ[R] M₂) (x : M)
  proof: by
  ext; simp

中文:
定理 comp_toSpanSingleton
  条件: [加法交换幺半群 M₂] [模 R M₂] (f : M ->ₗ[R] M₂) (x : M)
  证明: by
  ext; simp
-/
theorem comp_toSpanSingleton [AddCommMonoid M₂] [Module R M₂] (f : M ->ₗ[R] M₂) (x : M) :
    f ∘ₗ toSpanSingleton R M x = toSpanSingleton R M₂ (f x) := by
  ext; simp

/--
theorem `submoduleOf_span_singleton_of_mem` / 定理 `submoduleOf_span_singleton_of_mem`

English:
theorem submoduleOf_span_singleton_of_mem
  given: (N : Submodule R M) {x : M} (hx : x in N)
  proof: by
  ext y
  simp_rw [submoduleOf, mem_comap, subtype_apply, mem_span_singleton]
  aesop

中文:
定理 submoduleOf_span_singleton_of_mem
  条件: (N : 子模 R M) {x : M} (hx : x in N)
  证明: by
  ext y
  simp_rw [submoduleOf, mem_comap, subtype_apply, mem_span_singleton]
  aesop

Depends on / 依赖: mem_comap, mem_span_singleton, simp_rw, submoduleOf, subtype_apply
-/
theorem submoduleOf_span_singleton_of_mem (N : Submodule R M) {x : M} (hx : x in N) :
    (span R {x}).submoduleOf N = span R {⟨x, hx⟩} := by
  ext y
  simp_rw [submoduleOf, mem_comap, subtype_apply, mem_span_singleton]
  aesop

/--
lemma `ker_toSpanSingleton_eq_bot_iff` / 引理 `ker_toSpanSingleton_eq_bot_iff`

English:
lemma ker_toSpanSingleton_eq_bot_iff
  given: {x : R}
  proof: le_bot_iff.symm

中文:
引理 ker_toSpanSingleton_eq_bot_iff
  条件: {x : R}
  证明: le_bot_iff.symm
-/
@[simp] lemma ker_toSpanSingleton_eq_bot_iff {x : R} :
    ker (toSpanSingleton R R x) = ⊥ ↔ x in nonZeroDivisorsRight R := le_bot_iff.symm

end

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
variable {σ₁₂ : R ->+* R₂}
include σ₁₂

/--
theorem `eqOn_span_iff` / 定理 `eqOn_span_iff`

English:
theorem eqOn_span_iff
  given: {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂}
  proof: by
  rw [← le_eqLocus]; rw [span_le]; rfl

中文:
定理 eqOn_span_iff
  条件: {s : 集合 M} {f g : M ->ₛₗ[σ₁₂] M₂}
  证明: by
  rw [← le_eqLocus]; rw [span_le]; rfl

Depends on / 依赖: le_eqLocus, span_le
-/
theorem eqOn_span_iff {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} :
    Set.EqOn f g (span R s) ↔ Set.EqOn f g s := by
  rw [← le_eqLocus]; rw [span_le]; rfl

/--
theorem `eqOn_span'` / 定理 `eqOn_span'`

English:
theorem eqOn_span'
  given: {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s)
  proof: eqOn_span_iff.2 H

中文:
定理 eqOn_span'
  条件: {s : 集合 M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : 集合.EqOn f g s)
  证明: eqOn_span_iff.2 H

Depends on / 依赖: eqOn_span_iff
-/
theorem eqOn_span' {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) :
    Set.EqOn f g (span R s : Set M) :=
  eqOn_span_iff.2 H

/--
theorem `eqOn_span` / 定理 `eqOn_span`

English:
theorem eqOn_span
  given: {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) ⦃x⦄ (h : x in span R s)
  proof: eqOn_span' H h

中文:
定理 eqOn_span
  条件: {s : 集合 M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : 集合.EqOn f g s) ⦃x⦄ (h : x in span R s)
  证明: eqOn_span' H h

Depends on / 依赖: eqOn_span
-/
theorem eqOn_span {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) ⦃x⦄ (h : x in span R s) :
    f x = g x :=
  eqOn_span' H h

/--
theorem `ext_on` / 定理 `ext_on`

English:
theorem ext_on
  given: {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : Set.EqOn f g s)
  statement: f = g
  proof: DFunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)

中文:
定理 ext_on
  条件: {s : 集合 M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : 集合.EqOn f g s)
  结论: f = g
  证明: DFunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)

Depends on / 依赖: DFunLike, DFunLike.ext, eqOn_span, eq_top_iff
-/
theorem ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : Set.EqOn f g s) : f = g :=
  DFunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)

/--
theorem `ext_on_range` / 定理 `ext_on_range`

English:
theorem ext_on_range
  statement: {ι : Sort*} {v : ι -> M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R (Set.range v) = ⊤)
  proof: ext_on hv (Set.forall_mem_range.2 h)

中文:
定理 ext_on_range
  结论: {ι : 类型层*} {v : ι -> M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R (集合.range v) = ⊤)
  证明: ext_on hv (Set.forall_mem_range.2 h)

Depends on / 依赖: Set.forall_mem_range, ext_on, forall_mem_range
-/
theorem ext_on_range {ι : Sort*} {v : ι -> M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R (Set.range v) = ⊤)
    (h : forall i, f (v i) = g (v i)) : f = g :=
  ext_on hv (Set.forall_mem_range.2 h)

end AddCommMonoid

section IsDomain

variable [Semiring R] [AddCommMonoid M] [Module R M] [IsDomain R] [Module.IsTorsionFree R M]

variable (R) in
/--
theorem `ker_toSpanSingleton` / 定理 `ker_toSpanSingleton`

English:
theorem ker_toSpanSingleton
  given: {x : M} (h : x != 0)
  statement: LinearMap.ker (toSpanSingleton R M x) = ⊥
  proof: SetLike.ext fun _ => smul_eq_zero.trans or_iff_left_of_imp fun h' => (h h').elim

中文:
定理 ker_toSpanSingleton
  条件: {x : M} (h : x != 0)
  结论: 线性映射.ker (toSpanSingleton R M x) = ⊥
  证明: SetLike.ext fun _ => smul_eq_zero.trans or_iff_left_of_imp fun h' => (h h').elim

Depends on / 依赖: SetLike, SetLike.ext, or_iff_left_of_imp, smul_eq_zero, smul_eq_zero.trans
-/
theorem ker_toSpanSingleton {x : M} (h : x != 0) : LinearMap.ker (toSpanSingleton R M x) = ⊥ :=
SetLike.ext fun _ => smul_eq_zero.trans or_iff_left_of_imp fun h' => (h h').elim

end IsDomain

section Field

variable [Field K] [AddCommGroup V] [Module K V]

/--
theorem `span_singleton_sup_ker_eq_top` / 定理 `span_singleton_sup_ker_eq_top`

English:
theorem span_singleton_sup_ker_eq_top
  given: (f : V ->ₗ[K] K) {x : V} (hx : f x != 0)
  proof: top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩

中文:
定理 span_singleton_sup_ker_eq_top
  条件: (f : V ->ₗ[K] K) {x : V} (hx : f x != 0)
  证明: top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, Submodule.mem_sup, mem_span_singleton, mem_sup, top_unique
-/
theorem span_singleton_sup_ker_eq_top (f : V ->ₗ[K] K) {x : V} (hx : f x != 0) :
    K ∙ x ⊔ ker f = ⊤ :=
  top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩

end Field

end LinearMap

open LinearMap

namespace LinearEquiv

variable (R M)
variable [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (x : M)
  (h : x != 0)

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from `R` to the span of `x` given by $r \mapsto r \cdot x$. -/
noncomputable
/--
Definition of `toSpanNonzeroSingleton` / `toSpanNonzeroSingleton` 的定义

English:
definition toSpanNonzeroSingleton
  signature: : R ≃ₗ[R] R ∙ x
  body: LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (range_toSpanSingleton x))

中文:
定义 toSpanNonzeroSingleton
  签名: : R ≃ₗ[R] R ∙ x
  定义体: LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (range_toSpanSingleton x))

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, LinearEquiv.ofInjective, LinearEquiv.trans, LinearMap, LinearMap.toSpanSingleton, ker_eq_bot, ker_toSpanSingleton, ofInjective, range_toSpanSingleton, toSpanSingleton
-/
def toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (range_toSpanSingleton x))

/--
theorem `toSpanNonzeroSingleton_apply` / 定理 `toSpanNonzeroSingleton_apply`

English:
theorem toSpanNonzeroSingleton_apply
  given: (t : R)
  proof: by
  rfl

@[simp]

中文:
定理 toSpanNonzeroSingleton_apply
  条件: (t : R)
  证明: by
  rfl

@[simp]
-/
@[simp] theorem toSpanNonzeroSingleton_apply (t : R) :
    toSpanNonzeroSingleton R M x h t =
      (⟨t • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩ : R ∙ x) := by
  rfl

@[simp]
/--
lemma `toSpanNonzeroSingleton_symm_apply_smul` / 引理 `toSpanNonzeroSingleton_symm_apply_smul`

English:
lemma toSpanNonzeroSingleton_symm_apply_smul
  given: (m : R ∙ x)
  proof: congrArg Subtype.val apply_symm_apply (toSpanNonzeroSingleton R M x h) m

中文:
引理 toSpanNonzeroSingleton_symm_apply_smul
  条件: (m : R ∙ x)
  证明: congrArg Subtype.val apply_symm_apply (toSpanNonzeroSingleton R M x h) m

Depends on / 依赖: Subtype, Subtype.val, apply_symm_apply, toSpanNonzeroSingleton
-/
lemma toSpanNonzeroSingleton_symm_apply_smul (m : R ∙ x) :
    (toSpanNonzeroSingleton R M x h).symm m • x = m :=
congrArg Subtype.val apply_symm_apply (toSpanNonzeroSingleton R M x h) m

/--
theorem `toSpanNonzeroSingleton_one` / 定理 `toSpanNonzeroSingleton_one`

English:
theorem toSpanNonzeroSingleton_one
  proof: by simp

中文:
定理 toSpanNonzeroSingleton_one
  证明: by simp
-/
theorem toSpanNonzeroSingleton_one :
    LinearEquiv.toSpanNonzeroSingleton R M x h 1 =
      (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) := by simp

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from the span of `x` to `R` given by $r \cdot x \mapsto r$. -/
noncomputable
/--
Definition of `coord` / `coord` 的定义

English:
abbreviation coord
  signature: : R ∙ x ≃ₗ[R] R
  body: (toSpanNonzeroSingleton R M x h).symm

中文:
缩写 coord
  签名: : R ∙ x ≃ₗ[R] R
  定义体: (toSpanNonzeroSingleton R M x h).symm

Depends on / 依赖: toSpanNonzeroSingleton
-/
abbrev coord : R ∙ x ≃ₗ[R] R :=
  (toSpanNonzeroSingleton R M x h).symm

/--
theorem `coord_self` / 定理 `coord_self`

English:
theorem coord_self
  statement: (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) = 1
  proof: by
  rw [← toSpanNonzeroSingleton_one R M x h]; rw [LinearEquiv.symm_apply_apply]

中文:
定理 coord_self
  结论: (coord R M x h) (⟨x, 子模.mem_span_singleton_self x⟩ : R ∙ x) = 1
  证明: by
  rw [← toSpanNonzeroSingleton_one R M x h]; rw [LinearEquiv.symm_apply_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, symm_apply_apply, toSpanNonzeroSingleton_one
-/
theorem coord_self : (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) = 1 := by
  rw [← toSpanNonzeroSingleton_one R M x h]; rw [LinearEquiv.symm_apply_apply]

/--
theorem `coord_apply_smul` / 定理 `coord_apply_smul`

English:
theorem coord_apply_smul
  given: (y : Submodule.span R ({x} : Set M))
  statement: coord R M x h y • x = y
  proof: Subtype.ext_iff.1 (toSpanNonzeroSingleton R M x h).apply_symm_apply _

中文:
定理 coord_apply_smul
  条件: (y : 子模.span R ({x} : 集合 M))
  结论: coord R M x h y • x = y
  证明: Subtype.ext_iff.1 (toSpanNonzeroSingleton R M x h).apply_symm_apply _

Depends on / 依赖: Subtype, Subtype.ext_iff, apply_symm_apply, ext_iff, toSpanNonzeroSingleton
-/
theorem coord_apply_smul (y : Submodule.span R ({x} : Set M)) : coord R M x h y • x = y :=
Subtype.ext_iff.1 (toSpanNonzeroSingleton R M x h).apply_symm_apply _

end LinearEquiv
