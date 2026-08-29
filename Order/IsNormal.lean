/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.SuccPred.CompleteLinearOrder
public import Mathlib.Order.SuccPred.InitialSeg

/-!
# Normal functions

A normal function between well-orders is a strictly monotonic continuous function. Normal functions
arise chiefly in the context of cardinal and ordinal-valued functions.

We opt for an equivalent definition that's both simpler and often more convenient: a normal function
is a strictly monotonic function `f` such that at successor limits `a`, `f a` is the least upper
bound of `f b` with `b < a`.

See `Order.isNormal_iff_strictMono_and_continuous` for a proof that these notions are equivalent.
-/

public section

open Set

variable {α β γ : Type*} {a b : α} {f : α -> β} {g : β -> γ}

namespace Order

/-- A normal function between well-orders is a strictly monotonic continuous function. -/
@[mk_iff isNormal_iff']
/--
Definition of `IsNormal` / `IsNormal` 的定义

English:
structure IsNormal
  parameters: [LinearOrder α] [LinearOrder β] (f : α -> β)
  axioms and operations (2):
    - strictMono : StrictMono f
    - mem_lowerBounds_upperBounds_of_isSuccLimit({a : α} (ha : IsSuccLimit a)) : f a in lowerBounds (upperBounds (f '' Iio a))

中文:
结构 是正规
  参数: [线性序 α] [线性序 β] (f : α -> β)
  公理与运算 (2 个):
    - strictMono : 严格递增 f
    - mem_lowerBounds_upperBounds_of_isSuccLimit({a : α} (ha : 是SuccLimit a)) : f a in lowerBounds (upperBounds (f '' 左无界右开区间 a))
-/
structure IsNormal [LinearOrder α] [LinearOrder β] (f : α -> β) : Prop where
  strictMono : StrictMono f
  /-- This condition is the RHS of the `IsLUB (f '' Iio a) (f a)` predicate, which is sufficient
  since the LHS is implied by monotonicity. -/
  mem_lowerBounds_upperBounds_of_isSuccLimit {a : α} (ha : IsSuccLimit a) :
    f a in lowerBounds (upperBounds (f '' Iio a))

/--
theorem `isNormal_iff` / 定理 `isNormal_iff`

English:
theorem isNormal_iff
  given: [LinearOrder α] [LinearOrder β] {f : α -> β}
  proof: by
  simp [isNormal_iff', mem_lowerBounds, mem_upperBounds]

中文:
定理 isNormal_iff
  条件: [线性序 α] [线性序 β] {f : α -> β}
  证明: by
  simp [isNormal_iff', mem_lowerBounds, mem_upperBounds]

Depends on / 依赖: isNormal_iff, mem_lowerBounds, mem_upperBounds
-/
theorem isNormal_iff [LinearOrder α] [LinearOrder β] {f : α -> β} :
    IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall b < o, f b <= a) -> f o <= a := by
  simp [isNormal_iff', mem_lowerBounds, mem_upperBounds]

namespace IsNormal

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: {f : α -> β} (hf : IsNormal f)
  statement: Monotone f
  proof: hf.strictMono.monotone

中文:
定理 monotone
  条件: {f : α -> β} (hf : 是正规 f)
  结论: 递增 f
  证明: hf.strictMono.monotone
-/
protected theorem monotone {f : α -> β} (hf : IsNormal f) : Monotone f :=
  hf.strictMono.monotone

/--
theorem `isLUB_image_Iio_of_isSuccLimit` / 定理 `isLUB_image_Iio_of_isSuccLimit`

English:
theorem isLUB_image_Iio_of_isSuccLimit
  given: {f : α -> β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a)
  proof: by
  refine ⟨?_, hf.2 ha⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf.1 hb).le

中文:
定理 isLUB_image_Iio_of_isSuccLimit
  条件: {f : α -> β} (hf : 是正规 f) {a : α} (ha : 是SuccLimit a)
  证明: by
  refine ⟨?_, hf.2 ha⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf.1 hb).le
-/
theorem isLUB_image_Iio_of_isSuccLimit {f : α -> β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) :
    IsLUB (f '' Iio a) (f a) := by
  refine ⟨?_, hf.2 ha⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf.1 hb).le

/--
theorem `le_iff_forall_le` / 定理 `le_iff_forall_le`

English:
theorem le_iff_forall_le
  given: (hf : IsNormal f) (ha : IsSuccLimit a) {b : β}
  proof: by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

中文:
定理 le_iff_对任意_le
  条件: (hf : 是正规 f) (ha : 是SuccLimit a) {b : β}
  证明: by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

Depends on / 依赖: hf.isLUB_image_Iio_of_isSuccLimit, isLUB_image_Iio_of_isSuccLimit, isLUB_le_iff, mem_upperBounds
-/
theorem le_iff_forall_le (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    f a <= b ↔ forall a' < a, f a' <= b := by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

/--
theorem `lt_iff_exists_lt` / 定理 `lt_iff_exists_lt`

English:
theorem lt_iff_exists_lt
  given: (hf : IsNormal f) (ha : IsSuccLimit a) {b : β}
  proof: by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

中文:
定理 lt_iff_存在_lt
  条件: (hf : 是正规 f) (ha : 是SuccLimit a) {b : β}
  证明: by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

Depends on / 依赖: hf.isLUB_image_Iio_of_isSuccLimit, isLUB_image_Iio_of_isSuccLimit, lt_isLUB_iff, mem_upperBounds
-/
theorem lt_iff_exists_lt (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    b < f a ↔ exists a' < a, b < f a' := by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

/--
theorem `map_isSuccLimit` / 定理 `map_isSuccLimit`

English:
theorem map_isSuccLimit
  given: (hf : IsNormal f) (ha : IsSuccLimit a)
  statement: IsSuccLimit (f a)
  proof: by
  refine ⟨?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 ha.not_isMin
    exact not_isMin_iff.2 ⟨_, hf.strictMono hb⟩
  · obtain ⟨c, hc, hc'⟩ := (hf.lt_iff_exists_lt ha).1 hb.lt
    have hc' := hb.ge_of_gt hc'
    rw [hf.strictMono.le_iff_le] at hc'
    exact hc.not_ge hc'

中文:
定理 map_isSuccLimit
  条件: (hf : 是正规 f) (ha : 是SuccLimit a)
  结论: 是SuccLimit (f a)
  证明: by
  refine ⟨?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 ha.not_isMin
    exact not_isMin_iff.2 ⟨_, hf.strictMono hb⟩
  · obtain ⟨c, hc, hc'⟩ := (hf.lt_iff_exists_lt ha).1 hb.lt
    have hc' := hb.ge_of_gt hc'
    rw [hf.strictMono.le_iff_le] at hc'
    exact hc.not_ge hc'

Depends on / 依赖: ge_of_gt, ha.not_isMin, hb.ge_of_gt, hb.lt, hc.not_ge, hf.lt_iff_exists_lt, hf.strictMono, hf.strictMono.le_iff_le, le_iff_le, lt_iff_exists_lt, not_ge, not_isMin, not_isMin_iff, strictMono
-/
theorem map_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) : IsSuccLimit (f a) := by
  refine ⟨?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 ha.not_isMin
    exact not_isMin_iff.2 ⟨_, hf.strictMono hb⟩
  · obtain ⟨c, hc, hc'⟩ := (hf.lt_iff_exists_lt ha).1 hb.lt
    have hc' := hb.ge_of_gt hc'
    rw [hf.strictMono.le_iff_le] at hc'
    exact hc.not_ge hc'

/--
theorem `map_isLUB` / 定理 `map_isLUB`

English:
theorem map_isLUB
  given: (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
  proof: by
  refine ⟨?_, fun b hb => ?_⟩
  · simpa [mem_upperBounds, hf.strictMono.le_iff_le] using hs.1
  · by_cases ha : a in s
    · simp_all [mem_upperBounds]
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists

中文:
定理 map_isLUB
  条件: (hf : 是正规 f) {s : 集合 α} (hs : IsLUB s a) (hs' : s.非空)
  证明: by
  refine ⟨?_, fun b hb => ?_⟩
  · simpa [mem_upperBounds, hf.strictMono.le_iff_le] using hs.1
  · by_cases ha : a in s
    · simp_all [mem_upperBounds]
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists

Depends on / 依赖: exists_between, forall_mem_image, hf.strictMono, hf.strictMono.le_iff_le, hs.exists_between, hs.isSuccLimit_of_notMem, isSuccLimit_of_notMem, le.trans, le_iff_forall_le, le_iff_le, mem_upperBounds, simp_rw, strictMono
-/
theorem map_isLUB (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty) :
    IsLUB (f '' s) (f a) := by
  refine ⟨?_, fun b hb => ?_⟩
  · simpa [mem_upperBounds, hf.strictMono.le_iff_le] using hs.1
  · by_cases ha : a in s
    · simp_all [mem_upperBounds]
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists_between hc
      simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact (hf.strictMono hcd).le.trans (hb hd)

/--
theorem `_root_.InitialSeg.isNormal` / 定理 `_root_.InitialSeg.isNormal`

English:
theorem _root_.InitialSeg.isNormal
  given: (f : α <=i β)
  statement: IsNormal f where
  proof: f.strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2

中文:
定理 _root_.初始段.isNormal
  条件: (f : α <=i β)
  结论: 是正规 f where
  证明: f.strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2

Depends on / 依赖: f.strictMono, strictMono
-/
theorem _root_.InitialSeg.isNormal (f : α <=i β) : IsNormal f where
  strictMono := f.strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2

/--
theorem `_root_.PrincipalSeg.isNormal` / 定理 `_root_.PrincipalSeg.isNormal`

English:
theorem _root_.PrincipalSeg.isNormal
  given: (f : α <i β)
  statement: IsNormal f
  proof: (f : α <=i β).isNormal

中文:
定理 _root_.主段.isNormal
  条件: (f : α <i β)
  结论: 是正规 f
  证明: (f : α <=i β).isNormal

Depends on / 依赖: isNormal
-/
theorem _root_.PrincipalSeg.isNormal (f : α <i β) : IsNormal f :=
  (f : α <=i β).isNormal

/--
theorem `_root_.OrderIso.isNormal` / 定理 `_root_.OrderIso.isNormal`

English:
theorem _root_.OrderIso.isNormal
  given: (f : α ≃o β)
  statement: IsNormal f
  proof: f.toInitialSeg.isNormal

中文:
定理 _root_.OrderIso.isNormal
  条件: (f : α ≃o β)
  结论: 是正规 f
  证明: f.toInitialSeg.isNormal

Depends on / 依赖: f.toInitialSeg.isNormal, isNormal, toInitialSeg
-/
theorem _root_.OrderIso.isNormal (f : α ≃o β) : IsNormal f :=
  f.toInitialSeg.isNormal

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsNormal (@id α)
  proof: (OrderIso.refl _).isNormal

中文:
定理 id
  结论: 是正规 (@id α)
  证明: (OrderIso.refl _).isNormal

Depends on / 依赖: I.IsTwoSided, IsTwoSided, RingHomSurjective
-/
protected theorem id : IsNormal (@id α) :=
  (OrderIso.refl _).isNormal

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsNormal g) (hf : IsNormal f)
  statement: IsNormal (g ∘ f)
  proof: by
  refine ⟨hg.strictMono.comp hf.strictMono, fun ha b hb => ?_⟩
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc => (hg.strictMono hc).le.trans (hb hd)

中文:
定理 comp
  条件: (hg : 是正规 g) (hf : 是正规 f)
  结论: 是正规 (g ∘ f)
  证明: by
  refine ⟨hg.strictMono.comp hf.strictMono, fun ha b hb => ?_⟩
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc => (hg.strictMono hc).le.trans (hb hd)

Depends on / 依赖: Function, Function.comp_apply, comp_apply, forall_mem_image, hf.lt_iff_exists_lt, hf.map_isSuccLimit, hf.strictMono, hg.le_iff_forall_le, hg.strictMono, hg.strictMono.comp, le.trans, le_iff_forall_le, lt_iff_exists_lt, map_isSuccLimit, mem_upperBounds, simp_rw, strictMono
-/
theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
  refine ⟨hg.strictMono.comp hf.strictMono, fun ha b hb => ?_⟩
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc => (hg.strictMono hc).le.trans (hb hd)

/--
theorem `to_Iio` / 定理 `to_Iio`

English:
theorem to_Iio
  given: (hf : IsNormal f) (a : α)
  proof: by
  rw [isNormal_iff]
  refine ⟨fun x y h => hf.strictMono h, fun b hb c hc => hf.2 (hb.subtypeVal (isLowerSet_Iio _)) ?_⟩
  simpa [upperBounds] using! fun d hd => hc ⟨d, hd.trans b.2⟩ hd

中文:
定理 to_Iio
  条件: (hf : 是正规 f) (a : α)
  证明: by
  rw [isNormal_iff]
  refine ⟨fun x y h => hf.strictMono h, fun b hb c hc => hf.2 (hb.subtypeVal (isLowerSet_Iio _)) ?_⟩
  simpa [upperBounds] using! fun d hd => hc ⟨d, hd.trans b.2⟩ hd

Depends on / 依赖: hb.subtypeVal, hd.trans, hf.strictMono, isLowerSet_Iio, isNormal_iff, strictMono, subtypeVal, upperBounds
-/
theorem to_Iio (hf : IsNormal f) (a : α) :
    IsNormal (β := Iio (f a)) fun x : Iio a => ⟨f x.1, hf.strictMono x.2⟩ := by
  rw [isNormal_iff]
  refine ⟨fun x y h => hf.strictMono h, fun b hb c hc => hf.2 (hb.subtypeVal (isLowerSet_Iio _)) ?_⟩
  simpa [upperBounds] using! fun d hd => hc ⟨d, hd.trans b.2⟩ hd

end LinearOrder

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLinearOrder β]

/--
theorem `map_sSup` / 定理 `map_sSup`

English:
theorem map_sSup
  given: (hf : IsNormal f) {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s)
  proof: ((hf.map_isLUB (isLUB_csSup hs hs') hs).csSup_eq (hs.image f)).symm

中文:
定理 map_sSup
  条件: (hf : 是正规 f) {s : 集合 α} (hs : s.非空) (hs' : BddAbove s)
  证明: ((hf.map_isLUB (isLUB_csSup hs hs') hs).csSup_eq (hs.image f)).symm

Depends on / 依赖: csSup_eq, hf.map_isLUB, hs.image, isLUB_csSup, map_isLUB
-/
theorem map_sSup (hf : IsNormal f) {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf.map_isLUB (isLUB_csSup hs hs') hs).csSup_eq (hs.image f)).symm

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι} [Nonempty ι] {g : ι -> α} (hf : IsNormal f) (hg : BddAbove (range g))
  proof: by
  unfold iSup
  convert! map_sSup hf (range_nonempty g) hg
  ext
  simp

中文:
定理 map_iSup
  条件: {ι} [非空 ι] {g : ι -> α} (hf : 是正规 f) (hg : BddAbove (range g))
  证明: by
  unfold iSup
  convert! map_sSup hf (range_nonempty g) hg
  ext
  simp

Depends on / 依赖: convert, map_sSup, range_nonempty
-/
theorem map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : IsNormal f) (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  unfold iSup
  convert! map_sSup hf (range_nonempty g) hg
  ext
  simp

/--
theorem `iSup_iterate_mem_fixedPoints` / 定理 `iSup_iterate_mem_fixedPoints`

English:
theorem iSup_iterate_mem_fixedPoints
  statement: [WellFoundedLT α] {f : α -> α} (a : α) (hf : IsNormal f)
  proof: by
  rw [f.mem_fixedPoints_iff]; rw [hf.map_iSup hf']
  apply le_antisymm <;> refine ciSup_le fun n => ?_
  · rw [← f.iterate_succ_apply']
    exact le_ciSup hf' _
  · apply hf.strictMono.le_apply.trans
    apply (le_ciSup (hf'.mono _) n)
    simp_rw [← f.iterate_succ_apply']
    grind

中文:
定理 iSup_iterate_mem_fixedPoints
  结论: [WellFoundedLT α] {f : α -> α} (a : α) (hf : 是正规 f)
  证明: by
  rw [f.mem_fixedPoints_iff]; rw [hf.map_iSup hf']
  apply le_antisymm <;> refine ciSup_le fun n => ?_
  · rw [← f.iterate_succ_apply']
    exact le_ciSup hf' _
  · apply hf.strictMono.le_apply.trans
    apply (le_ciSup (hf'.mono _) n)
    simp_rw [← f.iterate_succ_apply']
    grind

Depends on / 依赖: ciSup_le, f.iterate_succ_apply, f.mem_fixedPoints_iff, hf.map_iSup, hf.strictMono.le_apply.trans, iterate_succ_apply, le_antisymm, le_apply, le_ciSup, map_iSup, mem_fixedPoints_iff, simp_rw, strictMono
-/
theorem iSup_iterate_mem_fixedPoints [WellFoundedLT α] {f : α -> α} (a : α) (hf : IsNormal f)
    (hf' : BddAbove (.range fun n => f^[n] a)) : ⨆ n, f^[n] a in f.fixedPoints := by
  rw [f.mem_fixedPoints_iff]; rw [hf.map_iSup hf']
  apply le_antisymm <;> refine ciSup_le fun n => ?_
  · rw [← f.iterate_succ_apply']
    exact le_ciSup hf' _
  · apply hf.strictMono.le_apply.trans
    apply (le_ciSup (hf'.mono _) n)
    simp_rw [← f.iterate_succ_apply']
    grind

/--
theorem `preimage_Iic` / 定理 `preimage_Iic`

English:
theorem preimage_Iic
  statement: (hf : IsNormal f) {x : β}
  proof: by
  refine le_antisymm (fun _ => le_csSup h₂) (fun y hy => ?_)
  obtain hy | rfl := hy.lt_or_eq
  · rw [lt_csSup_iff h₂ h₁] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (hf.strictMono hyz).le.trans hz
  · rw [mem_preimage, hf.map_sSup h₁ h₂]
    apply (csSup_le_csSup bddAbove_Iic _ (image_preimage

中文:
定理 preimage_Iic
  结论: (hf : 是正规 f) {x : β}
  证明: by
  refine le_antisymm (fun _ => le_csSup h₂) (fun y hy => ?_)
  obtain hy | rfl := hy.lt_or_eq
  · rw [lt_csSup_iff h₂ h₁] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (hf.strictMono hyz).le.trans hz
  · rw [mem_preimage, hf.map_sSup h₁ h₂]
    apply (csSup_le_csSup bddAbove_Iic _ (image_preimage

Depends on / 依赖: bddAbove_Iic, csSup_Iic, csSup_le_csSup, hf.map_sSup, hf.strictMono, hy.lt_or_eq, image_preimage_subset, le.trans, le_antisymm, le_csSup, lt_csSup_iff, lt_or_eq, map_sSup, mem_preimage, strictMono
-/
theorem preimage_Iic (hf : IsNormal f) {x : β}
    (h₁ : (f ⁻¹' Iic x).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic x)) :
    f ⁻¹' Iic x = Iic (sSup (f ⁻¹' Iic x)) := by
  refine le_antisymm (fun _ => le_csSup h₂) (fun y hy => ?_)
  obtain hy | rfl := hy.lt_or_eq
  · rw [lt_csSup_iff h₂ h₁] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (hf.strictMono hyz).le.trans hz
  · rw [mem_preimage, hf.map_sSup h₁ h₂]
    apply (csSup_le_csSup bddAbove_Iic _ (image_preimage_subset ..)).trans
    · rw [csSup_Iic]
    · simpa

/--
theorem `le_iff_le_sSup` / 定理 `le_iff_le_sSup`

English:
theorem le_iff_le_sSup
  statement: (hf : IsNormal f) {x : α} {y : β}
  proof: Set.ext_iff.1 (preimage_Iic hf h₁ h₂) x

中文:
定理 le_iff_le_sSup
  结论: (hf : 是正规 f) {x : α} {y : β}
  证明: Set.ext_iff.1 (preimage_Iic hf h₁ h₂) x

Depends on / 依赖: Set.ext_iff, ext_iff, preimage_Iic
-/
theorem le_iff_le_sSup (hf : IsNormal f) {x : α} {y : β}
    (h₁ : (f ⁻¹' Iic y).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic y)) :
    f x <= y ↔ x <= sSup (f ⁻¹' Iic y) :=
  Set.ext_iff.1 (preimage_Iic hf h₁ h₂) x

/--
theorem `le_iff_le_sSup'` / 定理 `le_iff_le_sSup'`

English:
theorem le_iff_le_sSup'
  statement: [WellFoundedLT α] {f : α -> α} (hf : IsNormal f) {x y : α}
  proof: hf.le_iff_le_sSup h ⟨y, fun _ => hf.strictMono.le_apply.trans⟩

中文:
定理 le_iff_le_sSup'
  结论: [WellFoundedLT α] {f : α -> α} (hf : 是正规 f) {x y : α}
  证明: hf.le_iff_le_sSup h ⟨y, fun _ => hf.strictMono.le_apply.trans⟩

Depends on / 依赖: hf.le_iff_le_sSup, hf.strictMono.le_apply.trans, le_apply, le_iff_le_sSup, strictMono
-/
theorem le_iff_le_sSup' [WellFoundedLT α] {f : α -> α} (hf : IsNormal f) {x y : α}
    (h : (f ⁻¹' Iic y).Nonempty) : f x <= y ↔ x <= sSup (f ⁻¹' Iic y) :=
  hf.le_iff_le_sSup h ⟨y, fun _ => hf.strictMono.le_apply.trans⟩

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrder β]

/--
theorem `apply_of_isSuccLimit` / 定理 `apply_of_isSuccLimit`

English:
theorem apply_of_isSuccLimit
  given: (hf : IsNormal f) (ha : IsSuccLimit a)
  proof: by
  convert! map_iSup hf _
  · exact ha.iSup_Iio.symm
  · exact ⟨⊥, ha.bot_lt⟩
  · use a
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hx.le

中文:
定理 apply_of_isSuccLimit
  条件: (hf : 是正规 f) (ha : 是SuccLimit a)
  证明: by
  convert! map_iSup hf _
  · exact ha.iSup_Iio.symm
  · exact ⟨⊥, ha.bot_lt⟩
  · use a
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hx.le

Depends on / 依赖: bot_lt, convert, ha.bot_lt, ha.iSup_Iio.symm, hx.le, iSup_Iio, map_iSup
-/
theorem apply_of_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) :
    f a = ⨆ b : Iio a, f b := by
  convert! map_iSup hf _
  · exact ha.iSup_Iio.symm
  · exact ⟨⊥, ha.bot_lt⟩
  · use a
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hx.le

end ConditionallyCompleteLinearOrderBot

section WellFoundedLT
variable [LinearOrder α] [WellFoundedLT α] [SuccOrder α] [LinearOrder β]

/--
theorem `of_succ_lt` / 定理 `of_succ_lt`

English:
theorem of_succ_lt
  proof: by
  refine ⟨fun a b => ?_, fun ha => (hl ha).2⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb => exact hb.not_lt.elim
  | succ b hb IH =>
    intro hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  | isSuccLimit 

中文:
定理 of_succ_lt
  证明: by
  refine ⟨fun a b => ?_, fun ha => (hl ha).2⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb => exact hb.not_lt.elim
  | succ b hb IH =>
    intro hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  | isSuccLimit 

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn, hab.not_isMax, hb.not_lt.elim, hb.succ_lt, isSuccLimit, limitRecOn, lt_succ_iff_eq_or_lt_of_not_isMax, lt_succ_of_not_isMax, mem_image_of_mem, not_isMax, not_lt, succ_lt, trans_le
-/
theorem of_succ_lt
    (hs : forall a, f a < f (succ a)) (hl : forall {a}, IsSuccLimit a -> IsLUB (f '' Iio a) (f a)) :
    IsNormal f := by
  refine ⟨fun a b => ?_, fun ha => (hl ha).2⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb => exact hb.not_lt.elim
  | succ b hb IH =>
    intro hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  | isSuccLimit b hb IH =>
    intro hab
    have hab' := hb.succ_lt hab
    exact (IH _ hab' (lt_succ_of_not_isMax hab.not_isMax)).trans_le
      ((hl hb).1 (mem_image_of_mem _ hab'))

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: [OrderBot α] {g : α -> β} (hf : IsNormal f) (hg : IsNormal g)
  proof: by
  constructor
  · simp_all
  rintro ⟨H₁, H₂⟩
  ext a
  induction a using SuccOrder.limitRecOn with
  | isMin a ha => rw [ha.eq_bot, H₁]
  | succ a ha IH => exact H₂ a IH
  | isSuccLimit a ha IH =>
    apply (hf.isLUB_image_Iio_of_isSuccLimit ha).unique
    convert! hg.isLUB_image_Iio_of_isSuccLim

中文:
定理 ext_iff
  条件: [有底序 α] {g : α -> β} (hf : 是正规 f) (hg : 是正规 g)
  证明: by
  constructor
  · simp_all
  rintro ⟨H₁, H₂⟩
  ext a
  induction a using SuccOrder.limitRecOn with
  | isMin a ha => rw [ha.eq_bot, H₁]
  | succ a ha IH => exact H₂ a IH
  | isSuccLimit a ha IH =>
    apply (hf.isLUB_image_Iio_of_isSuccLimit ha).unique
    convert! hg.isLUB_image_Iio_of_isSuccLim

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn, convert, eq_bot, ha.eq_bot, hf.isLUB_image_Iio_of_isSuccLimit, hg.isLUB_image_Iio_of_isSuccLimit, isLUB_image_Iio_of_isSuccLimit, isSuccLimit, limitRecOn, unique
-/
theorem ext_iff [OrderBot α] {g : α -> β} (hf : IsNormal f) (hg : IsNormal g) :
    f = g ↔ f ⊥ = g ⊥ ∧ forall a, f a = g a -> f (succ a) = g (succ a) := by
  constructor
  · simp_all
  rintro ⟨H₁, H₂⟩
  ext a
  induction a using SuccOrder.limitRecOn with
  | isMin a ha => rw [ha.eq_bot, H₁]
  | succ a ha IH => exact H₂ a IH
  | isSuccLimit a ha IH =>
    apply (hf.isLUB_image_Iio_of_isSuccLimit ha).unique
    convert! hg.isLUB_image_Iio_of_isSuccLimit ha using 1
    aesop

@[deprecated (since := "2026-03-22")] protected alias ext := IsNormal.ext_iff

/--
theorem `exists_map_le_lt_map_succ_of_exists_ge` / 定理 `exists_map_le_lt_map_succ_of_exists_ge`

English:
theorem exists_map_le_lt_map_succ_of_exists_ge
  statement: [NoMaxOrder α] [OrderBot α] [WellFoundedLT β]
  proof: by
  have : Nonempty β := ⟨x⟩
  let := WellFoundedLT.toOrderBot β
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot β
  have H : BddAbove (f ⁻¹' Iic x) :=
    have ⟨y, hy⟩ := hf'
⟨y, fun z hz => hf.strictMono.le_iff_le.1 hz.trans 

中文:
定理 存在_map_le_lt_map_succ_of_存在_ge
  结论: [NoMax序 α] [有底序 α] [WellFoundedLT β]
  证明: by
  have : Nonempty β := ⟨x⟩
  let := WellFoundedLT.toOrderBot β
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot β
  have H : BddAbove (f ⁻¹' Iic x) :=
    have ⟨y, hy⟩ := hf'
⟨y, fun z hz => hf.strictMono.le_iff_le.1 hz.trans 

Depends on / 依赖: BddAbove, Nonempty, Set.Iic, WellFoundedLT, WellFoundedLT.conditionallyCompleteLinearOrderBot, WellFoundedLT.toOrderBot, conditionallyCompleteLinearOrderBot, hf.le_iff_le_sSup, hf.strictMono.le_iff_le, hz.trans, le_iff_le, le_iff_le_sSup, lt_succ_iff, not_le, strictMono, toOrderBot
-/
theorem exists_map_le_lt_map_succ_of_exists_ge [NoMaxOrder α] [OrderBot α] [WellFoundedLT β]
    {f : α -> β} {x : β} (hf : IsNormal f) (hf' : exists y, x <= f y) (hx : f ⊥ <= x) :
    exists a, f a <= x ∧ x < f (succ a) := by
  have : Nonempty β := ⟨x⟩
  let := WellFoundedLT.toOrderBot β
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot β
  have H : BddAbove (f ⁻¹' Iic x) :=
    have ⟨y, hy⟩ := hf'
⟨y, fun z hz => hf.strictMono.le_iff_le.1 hz.trans hy⟩
  refine ⟨sSup (f ⁻¹' Set.Iic x), ?_, ?_⟩
  · rw [hf.le_iff_le_sSup ⟨⊥, hx⟩ H]
  · rw [← not_le, hf.le_iff_le_sSup ⟨⊥, hx⟩ H, not_le, lt_succ_iff]

/--
theorem `exists_map_le_lt_map_succ` / 定理 `exists_map_le_lt_map_succ`

English:
theorem exists_map_le_lt_map_succ
  statement: [NoMaxOrder α] [OrderBot α] {f : α -> α} {x : α}
  proof: exists_map_le_lt_map_succ_of_exists_ge hf ⟨x, hf.strictMono.le_apply⟩ hx

omit [SuccOrder α] in

中文:
定理 存在_map_le_lt_map_succ
  结论: [NoMax序 α] [有底序 α] {f : α -> α} {x : α}
  证明: exists_map_le_lt_map_succ_of_exists_ge hf ⟨x, hf.strictMono.le_apply⟩ hx

omit [SuccOrder α] in

Depends on / 依赖: exists_map_le_lt_map_succ_of_exists_ge, hf.strictMono.le_apply, le_apply, strictMono
-/
theorem exists_map_le_lt_map_succ [NoMaxOrder α] [OrderBot α] {f : α -> α} {x : α}
    (hf : IsNormal f) (hx : f ⊥ <= x) : exists a, f a <= x ∧ x < f (succ a) :=
  exists_map_le_lt_map_succ_of_exists_ge hf ⟨x, hf.strictMono.le_apply⟩ hx

omit [SuccOrder α] in
/--
theorem `dirSupClosed_range` / 定理 `dirSupClosed_range`

English:
theorem dirSupClosed_range
  given: {f : α -> α} (hf : IsNormal f)
  statement: DirSupClosed (range f)
  proof: by
  intro s hs hs₀ _ a ha
  have hf' : (f ⁻¹' s).Nonempty := by
    obtain ⟨b, hb⟩ := hs₀
    obtain ⟨c, rfl⟩ := hs hb
    exact ⟨c, hb⟩
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  have hfl : IsLUB (f ⁻¹' s) (sSup (f 

中文:
定理 dirSupClosed_range
  条件: {f : α -> α} (hf : 是正规 f)
  结论: DirSupClosed (range f)
  证明: by
  intro s hs hs₀ _ a ha
  have hf' : (f ⁻¹' s).Nonempty := by
    obtain ⟨b, hb⟩ := hs₀
    obtain ⟨c, rfl⟩ := hs hb
    exact ⟨c, hb⟩
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  have hfl : IsLUB (f ⁻¹' s) (sSup (f 

Depends on / 依赖: Nonempty, WellFoundedLT, WellFoundedLT.conditionallyCompleteLinearOrderBot, WellFoundedLT.toOrderBot, conditionallyCompleteLinearOrderBot, ha.unique, hf.map_isLUB, hf.strictMono.le_apply.trans, image_preimage_eq_of_subset, isLUB_csSup, le_apply, map_isLUB, mem_range_self, strictMono, toOrderBot, unique
-/
theorem dirSupClosed_range {f : α -> α} (hf : IsNormal f) : DirSupClosed (range f) := by
  intro s hs hs₀ _ a ha
  have hf' : (f ⁻¹' s).Nonempty := by
    obtain ⟨b, hb⟩ := hs₀
    obtain ⟨c, rfl⟩ := hs hb
    exact ⟨c, hb⟩
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  have hfl : IsLUB (f ⁻¹' s) (sSup (f ⁻¹' s)) :=
    isLUB_csSup hf' ⟨a, fun b hb => hf.strictMono.le_apply.trans (ha.1 hb)⟩
  have ha' := hf.map_isLUB hfl hf'
  rw [image_preimage_eq_of_subset hs] at ha'
  obtain rfl := ha.unique ha'
  exact mem_range_self _

end WellFoundedLT
end IsNormal
end Order
