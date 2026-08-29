/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Logic.Small.Set
public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Basic results on cardinal numbers

We provide a collection of basic results on cardinal numbers, in particular focusing on
finite/countable/small types and sets.

## Main definitions

* `Cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

@[expose] public section

assert_not_exists Field

open List (Vector)
open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Lifting cardinals to a higher universe -/

@[simp]
/--
lemma `mk_preimage_down` / 引理 `mk_preimage_down`

English:
lemma mk_preimage_down
  given: {s : Set α}
  statement: #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s)
  proof: by
  rw [← mk_uLift]; rw [Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s -> ULift s := fun x => ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

中文:
引理 mk_preimage_down
  条件: {s : Set α}
  结论: #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s)
  证明: by
  rw [← mk_uLift]; rw [Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s -> ULift s := fun x => ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

Depends on / 依赖: Bijective, Cardinal, Cardinal.eq, Equiv.ofBijective, Function, Function.Bijective, ULift.down, ULift.down_bijective, ULift.up, ULift.up_bijective.comp, down_bijective, mk_uLift, ofBijective, restrictPreimage, restrictPreimage_bijective, up_bijective
-/
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s) := by
  rw [← mk_uLift]; rw [Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s -> ULift s := fun x => ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

-- `simp` can't figure out universe levels: normal form is `lift_mk_shrink'`.
/--
theorem `lift_mk_shrink` / 定理 `lift_mk_shrink`

English:
theorem lift_mk_shrink
  given: (α : Type u) [Small.{v} α]
  proof: lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]

中文:
定理 lift_mk_shrink
  条件: (α : 类型u) [Small.{v} α]
  证明: lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]

Depends on / 依赖: equivShrink, lift_mk_eq
-/
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]
/--
theorem `lift_mk_shrink'` / 定理 `lift_mk_shrink'`

English:
theorem lift_mk_shrink'
  given: (α : Type u) [Small.{v} α]
  proof: lift_mk_shrink.{u, v, 0} α

@[simp]

中文:
定理 lift_mk_shrink'
  条件: (α : 类型u) [Small.{v} α]
  证明: lift_mk_shrink.{u, v, 0} α

@[simp]

Depends on / 依赖: lift_mk_shrink
-/
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α :=
  lift_mk_shrink.{u, v, 0} α

@[simp]
/--
theorem `lift_mk_shrink''` / 定理 `lift_mk_shrink''`

English:
theorem lift_mk_shrink''
  given: (α : Type max u v) [Small.{v} α]
  proof: by
  rw [← lift_umax]; rw [lift_mk_shrink.{max u v]; rw [v]; rw [0} α]; rw [← lift_umax]; rw [lift_id]

中文:
定理 lift_mk_shrink''
  条件: (α : Type max u v) [Small.{v} α]
  证明: by
  rw [← lift_umax]; rw [lift_mk_shrink.{max u v]; rw [v]; rw [0} α]; rw [← lift_umax]; rw [lift_id]

Depends on / 依赖: lift_id, lift_mk_shrink, lift_umax
-/
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = #α := by
  rw [← lift_umax]; rw [lift_mk_shrink.{max u v]; rw [v]; rw [0} α]; rw [← lift_umax]; rw [lift_id]

/--
theorem `prod_eq_of_fintype` / 定理 `prod_eq_of_fintype`

English:
theorem prod_eq_of_fintype
  given: {α : Type u} [h : Fintype α] (f : α -> Cardinal.{v})
  proof: by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    let := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f]; rw [← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty]; rw [Finset.prod_empty]; rw [lift_one]; r

中文:
定理 prod_eq_of_fintype
  条件: {α : 类型u} [h : Fintype α] (f : α -> Cardinal.{v})
  证明: by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    let := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f]; rw [← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty]; rw [Finset.prod_empty]; rw [lift_one]; r

Depends on / 依赖: Cardinal, Cardinal.prod, Equiv.piOptionEquivProd, Finset, Finset.prod_empty, Fintype, Fintype.induction_empty_option, Fintype.ofEquiv, Fintype.prod_opti, Fintype.univ_pempty, e.piCongrLeft, e.prod_comp, e.symm, h_fintype, induction_empty_option, lift_one, lift_prod, lift_umax, mk_congr, mk_eq_one
-/
theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α -> Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    let := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f]; rw [← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty]; rw [Finset.prod_empty]; rw [lift_one]; rw [Cardinal.prod]; rw [mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod]; rw [mk_congr Equiv.piOptionEquivProd]; rw [mk_prod]; rw [lift_umax.{v]; rw [u}]; rw [mk_out]; rw [←
        Cardinal.prod]; rw [lift_prod]; rw [Fintype.prod_option]; rw [lift_mul]; rw [← h fun a => f (some a)]
    simp only [lift_id]


/--
theorem `le_one_iff_subsingleton` / 定理 `le_one_iff_subsingleton`

English:
theorem le_one_iff_subsingleton
  given: {α : Type u}
  statement: #α <= 1 ↔ Subsingleton α
  proof: ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]

中文:
定理 le_one_iff_subsingleton
  条件: {α : 类型u}
  结论: #α <= 1 ↔ Subsingleton α
  证明: ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, ULift.up, f.injective, injective
-/
theorem le_one_iff_subsingleton {α : Type u} : #α <= 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]
/--
theorem `mk_le_one_iff_set_subsingleton` / 定理 `mk_le_one_iff_set_subsingleton`

English:
theorem mk_le_one_iff_set_subsingleton
  given: {s : Set α}
  statement: #s <= 1 ↔ s.Subsingleton
  proof: le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton

中文:
定理 mk_le_one_iff_set_subsingleton
  条件: {s : Set α}
  结论: #s <= 1 ↔ s.Subsingleton
  证明: le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton

Depends on / 依赖: le_one_iff_subsingleton, le_one_iff_subsingleton.trans, s.subsingleton_coe, subsingleton_coe
-/
theorem mk_le_one_iff_set_subsingleton {s : Set α} : #s <= 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton


/--
theorem `one_lt_iff_nontrivial` / 定理 `one_lt_iff_nontrivial`

English:
theorem one_lt_iff_nontrivial
  given: {α : Type u}
  statement: 1 < #α ↔ Nontrivial α
  proof: by
  rw [← not_le]; rw [le_one_iff_subsingleton]; rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

中文:
定理 one_lt_iff_nontrivial
  条件: {α : 类型u}
  结论: 1 < #α ↔ Nontrivial α
  证明: by
  rw [← not_le]; rw [le_one_iff_subsingleton]; rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, le_one_iff_subsingleton, not_le, not_nontrivial_iff_subsingleton, not_not
-/
theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α := by
  rw [← not_le]; rw [le_one_iff_subsingleton]; rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

/--
lemma `sInf_eq_zero_iff` / 引理 `sInf_eq_zero_iff`

English:
lemma sInf_eq_zero_iff
  given: {s : Set Cardinal}
  statement: sInf s = 0 ↔ s = ∅ ∨ exists a in s, a = 0
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

中文:
引理 sInf_eq_zero_iff
  条件: {s : Set Cardinal}
  结论: sInf s = 0 ↔ s = ∅ ∨ 存在 a in s, a = 0
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

Depends on / 依赖: Cardinal, Cardinal.sInf_empty, Or.inl, Or.inr, csInf_le, csInf_mem, eq_bot_iff, eq_empty_or_nonempty, s.eq_empty_or_nonempty, sInf_empty
-/
lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ exists a in s, a = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

/--
lemma `iInf_eq_zero_iff` / 引理 `iInf_eq_zero_iff`

English:
lemma iInf_eq_zero_iff
  given: {ι : Sort*} {f : ι -> Cardinal}
  proof: by
  simp [iInf, sInf_eq_zero_iff]

中文:
引理 iInf_eq_zero_iff
  条件: {ι : Sort*} {f : ι -> Cardinal}
  证明: by
  simp [iInf, sInf_eq_zero_iff]

Depends on / 依赖: sInf_eq_zero_iff
-/
lemma iInf_eq_zero_iff {ι : Sort*} {f : ι -> Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ exists i, f i = 0 := by
  simp [iInf, sInf_eq_zero_iff]

/--
theorem `iSup_of_empty` / 定理 `iSup_of_empty`

English:
theorem iSup_of_empty
  given: {ι} (f : ι -> Cardinal) [IsEmpty ι]
  statement: iSup f = 0
  proof: ciSup_of_empty f

@[simp]

中文:
定理 iSup_of_empty
  条件: {ι} (f : ι -> Cardinal) [IsEmpty ι]
  结论: iSup f = 0
  证明: ciSup_of_empty f

@[simp]
-/
protected theorem iSup_of_empty {ι} (f : ι -> Cardinal) [IsEmpty ι] : iSup f = 0 :=
  ciSup_of_empty f

@[simp]
/--
theorem `lift_sInf` / 定理 `lift_sInf`

English:
theorem lift_sInf
  given: (s : Set Cardinal)
  statement: lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]

中文:
定理 lift_sInf
  条件: (s : Set Cardinal)
  结论: lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]

Depends on / 依赖: eq_empty_or_nonempty, lift_monotone, lift_monotone.map_csInf, map_csInf
-/
theorem lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]
/--
theorem `lift_iInf` / 定理 `lift_iInf`

English:
theorem lift_iInf
  given: {ι} (f : ι -> Cardinal)
  statement: lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i)
  proof: by
  unfold iInf
  convert! lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

中文:
定理 lift_iInf
  条件: {ι} (f : ι -> Cardinal)
  结论: lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i)
  证明: by
  unfold iInf
  convert! lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

Depends on / 依赖: comp_apply, convert, lift_sInf, range_comp, simp_rw
-/
theorem lift_iInf {ι} (f : ι -> Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i) := by
  unfold iInf
  convert! lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

end Cardinal

/-! ### Small sets of cardinals -/

namespace Cardinal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `small_Iic` / 实例 `small_Iic`

English:
instance small_Iic
  signature: (a : Cardinal.{u})
  body: by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

中文:
实例 small_Iic
  签名: (a : Cardinal.{u})
  定义体: by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

Depends on / 依赖: a.out, le_mk_iff_exists_set, mk_out, mk_set_le, small_of_surjective
-/
instance small_Iic (a : Cardinal.{u}) : Small.{u} (Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

/--
Instance `small_Iio` / 实例 `small_Iio`

English:
instance small_Iio
  signature: (a : Cardinal.{u})
  body: small_subset Iio_subset_Iic_self

中文:
实例 small_Iio
  签名: (a : Cardinal.{u})
  定义体: small_subset Iio_subset_Iic_self

Depends on / 依赖: Iio_subset_Iic_self, small_subset
-/
instance small_Iio (a : Cardinal.{u}) : Small.{u} (Iio a) := small_subset Iio_subset_Iic_self
/--
Instance `small_Icc` / 实例 `small_Icc`

English:
instance small_Icc
  signature: (a b : Cardinal.{u})
  body: small_subset Icc_subset_Iic_self

中文:
实例 small_Icc
  签名: (a b : Cardinal.{u})
  定义体: small_subset Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, small_subset
-/
instance small_Icc (a b : Cardinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
/--
Instance `small_Ico` / 实例 `small_Ico`

English:
instance small_Ico
  signature: (a b : Cardinal.{u})
  body: small_subset Ico_subset_Iio_self

中文:
实例 small_Ico
  签名: (a b : Cardinal.{u})
  定义体: small_subset Ico_subset_Iio_self

Depends on / 依赖: Ico_subset_Iio_self, small_subset
-/
instance small_Ico (a b : Cardinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
/--
Instance `small_Ioc` / 实例 `small_Ioc`

English:
instance small_Ioc
  signature: (a b : Cardinal.{u})
  body: small_subset Ioc_subset_Iic_self

中文:
实例 small_Ioc
  签名: (a b : Cardinal.{u})
  定义体: small_subset Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, small_subset
-/
instance small_Ioc (a b : Cardinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self
/--
Instance `small_Ioo` / 实例 `small_Ioo`

English:
instance small_Ioo
  signature: (a b : Cardinal.{u})
  body: small_subset Ioo_subset_Iio_self

中文:
实例 small_Ioo
  签名: (a b : Cardinal.{u})
  定义体: small_subset Ioo_subset_Iio_self

Depends on / 依赖: Ioo_subset_Iio_self, small_subset
-/
instance small_Ioo (a b : Cardinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self

/--
theorem `bddAbove_iff_small` / 定理 `bddAbove_iff_small`

English:
theorem bddAbove_iff_small
  given: {s : Set Cardinal.{u}}
  statement: BddAbove s ↔ Small.{u} s
  proof: ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun _ h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    use sum.{u, u} fun x => e.symm x
    intro a ha
    simpa using le_sum (fun x => e.symm x) (e ⟨a, ha⟩)⟩

中文:
定理 bddAbove_iff_small
  条件: {s : Set Cardinal.{u}}
  结论: BddAbove s ↔ Small.{u} s
  证明: ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun _ h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    use sum.{u, u} fun x => e.symm x
    intro a ha
    simpa using le_sum (fun x => e.symm x) (e ⟨a, ha⟩)⟩

Depends on / 依赖: e.symm, le_sum, small_subset
-/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun _ h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    use sum.{u, u} fun x => e.symm x
    intro a ha
    simpa using le_sum (fun x => e.symm x) (e ⟨a, ha⟩)⟩

/--
theorem `bddAbove_of_small` / 定理 `bddAbove_of_small`

English:
theorem bddAbove_of_small
  given: {s : Set Cardinal.{u}} [h : Small.{u} s]
  statement: BddAbove s
  proof: bddAbove_iff_small.2 h

@[deprecated bddAbove_of_small (since := "2026-04-04")]

中文:
定理 bddAbove_of_small
  条件: {s : Set Cardinal.{u}} [h : Small.{u} s]
  结论: BddAbove s
  证明: bddAbove_iff_small.2 h

@[deprecated bddAbove_of_small (since := "2026-04-04")]

Depends on / 依赖: bddAbove_iff_small
-/
theorem bddAbove_of_small {s : Set Cardinal.{u}} [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h

@[deprecated bddAbove_of_small (since := "2026-04-04")]
/--
theorem `bddAbove_range` / 定理 `bddAbove_range`

English:
theorem bddAbove_range
  given: {ι : Type*} [Small.{u} ι] (f : ι -> Cardinal.{u})
  statement: BddAbove (Set.range f)
  proof: bddAbove_of_small

中文:
定理 bddAbove_range
  条件: {ι : 类型} [Small.{u} ι] (f : ι -> Cardinal.{u})
  结论: BddAbove (Set.range f)
  证明: bddAbove_of_small

Depends on / 依赖: bddAbove_of_small
-/
theorem bddAbove_range {ι : Type*} [Small.{u} ι] (f : ι -> Cardinal.{u}) : BddAbove (Set.range f) :=
  bddAbove_of_small

/--
theorem `bddAbove_image` / 定理 `bddAbove_image`

English:
theorem bddAbove_image
  statement: (f : Cardinal.{u} -> Cardinal.{max u v}) {s : Set Cardinal.{u}}
  proof: by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _

中文:
定理 bddAbove_image
  结论: (f : Cardinal.{u} -> Cardinal.{max u v}) {s : Set Cardinal.{u}}
  证明: by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _

Depends on / 依赖: bddAbove_iff_small, small_lift
-/
theorem bddAbove_image (f : Cardinal.{u} -> Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _

/--
theorem `bddAbove_range_comp` / 定理 `bddAbove_range_comp`

English:
theorem bddAbove_range_comp
  statement: {ι : Type u} {f : ι -> Cardinal.{v}} (hf : BddAbove (range f))
  proof: by
  rw [range_comp]
  exact bddAbove_image g hf

中文:
定理 bddAbove_range_comp
  结论: {ι : 类型u} {f : ι -> Cardinal.{v}} (hf : BddAbove (range f))
  证明: by
  rw [range_comp]
  exact bddAbove_image g hf

Depends on / 依赖: bddAbove_image, range_comp
-/
theorem bddAbove_range_comp {ι : Type u} {f : ι -> Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} -> Cardinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image g hf

/--
theorem `_root_.not_small_cardinal` / 定理 `_root_.not_small_cardinal`

English:
theorem _root_.not_small_cardinal
  statement: ¬ Small.{u} Cardinal.{max u v}
  proof: by
  intro h
  have := small_lift.{_, v} Cardinal.{max u v}
  rw [← small_univ_iff]; rw [← bddAbove_iff_small] at this
  exact not_bddAbove_univ this

中文:
定理 _root_.not_small_cardinal
  结论: ¬ Small.{u} Cardinal.{max u v}
  证明: by
  intro h
  have := small_lift.{_, v} Cardinal.{max u v}
  rw [← small_univ_iff]; rw [← bddAbove_iff_small] at this
  exact not_bddAbove_univ this

Depends on / 依赖: Cardinal, bddAbove_iff_small, not_bddAbove_univ, small_lift, small_univ_iff
-/
theorem _root_.not_small_cardinal : ¬ Small.{u} Cardinal.{max u v} := by
  intro h
  have := small_lift.{_, v} Cardinal.{max u v}
  rw [← small_univ_iff]; rw [← bddAbove_iff_small] at this
  exact not_bddAbove_univ this

/--
Instance `uncountable` / 实例 `uncountable`

English:
instance uncountable
  signature: : Uncountable Cardinal.{u}
  body: Uncountable.of_not_small not_small_cardinal.{u}

中文:
实例 uncountable
  签名: : Uncountable Cardinal.{u}
  定义体: Uncountable.of_not_small not_small_cardinal.{u}

Depends on / 依赖: Uncountable, Uncountable.of_not_small, not_small_cardinal, of_not_small
-/
instance uncountable : Uncountable Cardinal.{u} :=
  Uncountable.of_not_small not_small_cardinal.{u}


/--
theorem `sum_le_lift_mk_mul_iSup_lift` / 定理 `sum_le_lift_mk_mul_iSup_lift`

English:
theorem sum_le_lift_mk_mul_iSup_lift
  given: {ι : Type u} (f : ι -> Cardinal.{v})
  proof: by
  rw [← (sum f).lift_id]; rw [lift_sum]; rw [← lift_umax.{u]; rw [v}]; rw [← (⨆ i]; rw [lift (f i)).lift_id]; rw [lift_umax.{max v u]; rw [u}]; rw [← sum_const]
  refine sum_le_sum _ _ fun i => ?_
  rw [lift_umax.{v]; rw [u}]
  exact le_ciSup bddAbove_of_small i

中文:
定理 sum_le_lift_mk_mul_iSup_lift
  条件: {ι : 类型u} (f : ι -> Cardinal.{v})
  证明: by
  rw [← (sum f).lift_id]; rw [lift_sum]; rw [← lift_umax.{u]; rw [v}]; rw [← (⨆ i]; rw [lift (f i)).lift_id]; rw [lift_umax.{max v u]; rw [u}]; rw [← sum_const]
  refine sum_le_sum _ _ fun i => ?_
  rw [lift_umax.{v]; rw [u}]
  exact le_ciSup bddAbove_of_small i

Depends on / 依赖: bddAbove_of_small, le_ciSup, lift_id, lift_sum, lift_umax, sum_const, sum_le_sum
-/
theorem sum_le_lift_mk_mul_iSup_lift {ι : Type u} (f : ι -> Cardinal.{v}) :
    sum f <= lift #ι * ⨆ i, lift (f i) := by
  rw [← (sum f).lift_id]; rw [lift_sum]; rw [← lift_umax.{u]; rw [v}]; rw [← (⨆ i]; rw [lift (f i)).lift_id]; rw [lift_umax.{max v u]; rw [u}]; rw [← sum_const]
  refine sum_le_sum _ _ fun i => ?_
  rw [lift_umax.{v]; rw [u}]
  exact le_ciSup bddAbove_of_small i

/--
theorem `sum_le_lift_mk_mul_iSup` / 定理 `sum_le_lift_mk_mul_iSup`

English:
theorem sum_le_lift_mk_mul_iSup
  given: {ι : Type u} (f : ι -> Cardinal.{max u v})
  proof: by
  simpa [← lift_umax] using sum_le_lift_mk_mul_iSup_lift f

中文:
定理 sum_le_lift_mk_mul_iSup
  条件: {ι : 类型u} (f : ι -> Cardinal.{max u v})
  证明: by
  simpa [← lift_umax] using sum_le_lift_mk_mul_iSup_lift f

Depends on / 依赖: lift_umax, sum_le_lift_mk_mul_iSup_lift
-/
theorem sum_le_lift_mk_mul_iSup {ι : Type u} (f : ι -> Cardinal.{max u v}) :
    sum f <= lift #ι * ⨆ i, f i := by
  simpa [← lift_umax] using sum_le_lift_mk_mul_iSup_lift f

/--
theorem `sum_le_mk_mul_iSup` / 定理 `sum_le_mk_mul_iSup`

English:
theorem sum_le_mk_mul_iSup
  given: {ι : Type u} (f : ι -> Cardinal.{u})
  statement: sum f <= #ι * ⨆ i, f i
  proof: by
  simpa using sum_le_lift_mk_mul_iSup_lift f

中文:
定理 sum_le_mk_mul_iSup
  条件: {ι : 类型u} (f : ι -> Cardinal.{u})
  结论: sum f <= #ι * ⨆ i, f i
  证明: by
  simpa using sum_le_lift_mk_mul_iSup_lift f

Depends on / 依赖: sum_le_lift_mk_mul_iSup_lift
-/
theorem sum_le_mk_mul_iSup {ι : Type u} (f : ι -> Cardinal.{u}) : sum f <= #ι * ⨆ i, f i := by
  simpa using sum_le_lift_mk_mul_iSup_lift f

/--
theorem `lift_sSup` / 定理 `lift_sSup`

English:
theorem lift_sSup
  given: {s : Set Cardinal} (hs : BddAbove s)
  proof: by
  apply ((le_csSup_iff' (bddAbove_image.{_, u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
exact h fun a ha => lift_le.1 hc (mem_imag

中文:
定理 lift_sSup
  条件: {s : Set Cardinal} (hs : BddAbove s)
  证明: by
  apply ((le_csSup_iff' (bddAbove_image.{_, u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
exact h fun a ha => lift_le.1 hc (mem_imag

Depends on / 依赖: Cardinal, Cardinal.mem_range_lift_of_le, antisymm, bddAbove_image, csSup_le, csSup_le_iff, le_csSup, le_csSup_iff, lift_le, mem_image_of_mem, mem_range_lift_of_le, not_le, simp_rw
-/
theorem lift_sSup {s : Set Cardinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (bddAbove_image.{_, u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
exact h fun a ha => lift_le.1 hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/--
theorem `lift_iSup` / 定理 `lift_iSup`

English:
theorem lift_iSup
  given: {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f))
  proof: by
  rw [iSup]; rw [iSup]; rw [lift_sSup hf]; rw [← range_comp]
  simp [Function.comp_def]

中文:
定理 lift_iSup
  条件: {ι : 类型v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f))
  证明: by
  rw [iSup]; rw [iSup]; rw [lift_sSup hf]; rw [← range_comp]
  simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, lift_sSup, range_comp
-/
theorem lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup]; rw [iSup]; rw [lift_sSup hf]; rw [← range_comp]
  simp [Function.comp_def]

/--
theorem `lift_iSup_le` / 定理 `lift_iSup_le`

English:
theorem lift_iSup_le
  statement: {ι : Type v} {f : ι -> Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
  proof: by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]

中文:
定理 lift_iSup_le
  结论: {ι : 类型v} {f : ι -> Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
  证明: by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]

Depends on / 依赖: ciSup_le, lift_iSup
-/
theorem lift_iSup_le {ι : Type v} {f : ι -> Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : forall i, lift.{u} (f i) <= t) : lift.{u} (iSup f) <= t := by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]
/--
theorem `lift_iSup_le_iff` / 定理 `lift_iSup_le_iff`

English:
theorem lift_iSup_le_iff
  statement: {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f))
  proof: by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_, _, u} hf _)

中文:
定理 lift_iSup_le_iff
  结论: {ι : 类型v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f))
  证明: by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_, _, u} hf _)

Depends on / 依赖: bddAbove_range_comp, ciSup_le_iff, lift_iSup
-/
theorem lift_iSup_le_iff {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (iSup f) <= t ↔ forall i, lift.{u} (f i) <= t := by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_, _, u} hf _)

/--
theorem `lift_iSup_le_lift_iSup` / 定理 `lift_iSup_le_lift_iSup`

English:
theorem lift_iSup_le_lift_iSup
  statement: {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{w}}
  proof: by
  rw [lift_iSup hf]; rw [lift_iSup hf']
  exact ciSup_mono_of_forall_exists' (bddAbove_range_comp.{_, _, w} hf' _) fun i => ⟨_, h i⟩

中文:
定理 lift_iSup_le_lift_iSup
  结论: {ι : 类型v} {ι' : 类型v'} {f : ι -> Cardinal.{w}}
  证明: by
  rw [lift_iSup hf]; rw [lift_iSup hf']
  exact ciSup_mono_of_forall_exists' (bddAbove_range_comp.{_, _, w} hf' _) fun i => ⟨_, h i⟩

Depends on / 依赖: bddAbove_range_comp, ciSup_mono_of_forall_exists, lift_iSup
-/
theorem lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{w}}
    {f' : ι' -> Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι -> ι'}
    (h : forall i, lift.{w'} (f i) <= lift.{w} (f' (g i))) : lift.{w'} (iSup f) <= lift.{w} (iSup f') := by
  rw [lift_iSup hf]; rw [lift_iSup hf']
  exact ciSup_mono_of_forall_exists' (bddAbove_range_comp.{_, _, w} hf' _) fun i => ⟨_, h i⟩

/--
theorem `lift_iSup_le_lift_iSup'` / 定理 `lift_iSup_le_lift_iSup'`

English:
theorem lift_iSup_le_lift_iSup'
  statement: {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{v}}
  proof: lift_iSup_le_lift_iSup hf hf' h

中文:
定理 lift_iSup_le_lift_iSup'
  结论: {ι : 类型v} {ι' : 类型v'} {f : ι -> Cardinal.{v}}
  证明: lift_iSup_le_lift_iSup hf hf' h

Depends on / 依赖: DiscreteTopology, DiscreteTopology.firstCountableTopology, firstCountableTopology, lift_iSup_le_lift_iSup
-/
theorem lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{v}}
    {f' : ι' -> Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι -> ι')
    (h : forall i, lift.{v'} (f i) <= lift.{v} (f' (g i))) : lift.{v'} (iSup f) <= lift.{v} (iSup f') :=
  lift_iSup_le_lift_iSup hf hf' h

/--
theorem `lift_iSup_le_sum` / 定理 `lift_iSup_le_sum`

English:
theorem lift_iSup_le_sum
  given: {ι : Type u} [Small.{v} ι] (f : ι -> Cardinal.{v})
  proof: by
  rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => lift_le_sum f i

中文:
定理 lift_iSup_le_sum
  条件: {ι : 类型u} [Small.{v} ι] (f : ι -> Cardinal.{v})
  证明: by
  rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => lift_le_sum f i

Depends on / 依赖: DiscreteTopology, DiscreteTopology.secondCountableTopology_of_countable, bddAbove_of_small, ciSup_le, lift_iSup, lift_le_sum, secondCountableTopology_of_countable
-/
theorem lift_iSup_le_sum {ι : Type u} [Small.{v} ι] (f : ι -> Cardinal.{v}) :
    lift (⨆ i, f i) <= sum f := by
  rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => lift_le_sum f i


/--
theorem `mk_finset_of_fintype` / 定理 `mk_finset_of_fintype`

English:
theorem mk_finset_of_fintype
  given: [Fintype α]
  statement: #(Finset α) = 2 ^ Fintype.card α
  proof: by
  simp

@[simp, norm_cast]

中文:
定理 mk_finset_of_fintype
  条件: [Fintype α]
  结论: #(Finset α) = 2 ^ Fintype.card α
  证明: by
  simp

@[simp, norm_cast]
-/
theorem mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α := by
  simp

@[simp, norm_cast]
/--
lemma `succ_natCast` / 引理 `succ_natCast`

English:
lemma succ_natCast
  given: (n : Nat)
  statement: Order.succ (n : Cardinal) = n + 1
  proof: by
  refine (succ_le_of_lt ?_).antisymm (add_one_le_of_lt <| lt_succ _)
  rw [← Nat.cast_succ]
  exact Nat.cast_lt.2 (Nat.lt_succ_self _)

@[deprecated succ_natCast (since := "2026-03-21")]

中文:
引理 succ_natCast
  条件: (n : 自然数)
  结论: Order.succ (n : Cardinal) = n + 1
  证明: by
  refine (succ_le_of_lt ?_).antisymm (add_one_le_of_lt <| lt_succ _)
  rw [← Nat.cast_succ]
  exact Nat.cast_lt.2 (Nat.lt_succ_self _)

@[deprecated succ_natCast (since := "2026-03-21")]

Depends on / 依赖: Nat.cast_lt, Nat.cast_succ, Nat.lt_succ_self, add_one_le_of_lt, antisymm, cast_lt, cast_succ, lt_succ, lt_succ_self, succ_le_of_lt
-/
lemma succ_natCast (n : Nat) : Order.succ (n : Cardinal) = n + 1 := by
  refine (succ_le_of_lt ?_).antisymm (add_one_le_of_lt <| lt_succ _)
  rw [← Nat.cast_succ]
  exact Nat.cast_lt.2 (Nat.lt_succ_self _)

@[deprecated succ_natCast (since := "2026-03-21")]
/--
theorem `nat_succ` / 定理 `nat_succ`

English:
theorem nat_succ
  given: (n : Nat)
  statement: (n.succ : Cardinal) = succ ↑n
  proof: by
  simp

@[simp]

中文:
定理 nat_succ
  条件: (n : 自然数)
  结论: (n.succ : Cardinal) = succ ↑n
  证明: by
  simp

@[simp]
-/
theorem nat_succ (n : Nat) : (n.succ : Cardinal) = succ ↑n := by
  simp

@[simp]
/--
lemma `natCast_add_one_le_iff` / 引理 `natCast_add_one_le_iff`

English:
lemma natCast_add_one_le_iff
  given: {n : Nat} {c : Cardinal}
  statement: n + 1 <= c ↔ n < c
  proof: by
  rw [← Order.succ_le_iff]; rw [succ_natCast]

@[simp]

中文:
引理 natCast_add_one_le_iff
  条件: {n : 自然数} {c : Cardinal}
  结论: n + 1 <= c ↔ n < c
  证明: by
  rw [← Order.succ_le_iff]; rw [succ_natCast]

@[simp]

Depends on / 依赖: Order.succ_le_iff, succ_le_iff, succ_natCast
-/
lemma natCast_add_one_le_iff {n : Nat} {c : Cardinal} : n + 1 <= c ↔ n < c := by
  rw [← Order.succ_le_iff]; rw [succ_natCast]

@[simp]
/--
lemma `lt_natCast_add_one_iff` / 引理 `lt_natCast_add_one_iff`

English:
lemma lt_natCast_add_one_iff
  given: {n : Nat} {c : Cardinal}
  statement: c < n + 1 ↔ c <= n
  proof: by
  rw [← Order.lt_succ_iff]; rw [succ_natCast]

中文:
引理 lt_natCast_add_one_iff
  条件: {n : 自然数} {c : Cardinal}
  结论: c < n + 1 ↔ c <= n
  证明: by
  rw [← Order.lt_succ_iff]; rw [succ_natCast]

Depends on / 依赖: Order.lt_succ_iff, lt_succ_iff, succ_natCast
-/
lemma lt_natCast_add_one_iff {n : Nat} {c : Cardinal} : c < n + 1 ↔ c <= n := by
  rw [← Order.lt_succ_iff]; rw [succ_natCast]

/--
lemma `two_le_iff_one_lt` / 引理 `two_le_iff_one_lt`

English:
lemma two_le_iff_one_lt
  given: {c : Cardinal}
  statement: 2 <= c ↔ 1 < c
  proof: by
  convert! natCast_add_one_le_iff
  norm_cast

@[simp]

中文:
引理 two_le_iff_one_lt
  条件: {c : Cardinal}
  结论: 2 <= c ↔ 1 < c
  证明: by
  convert! natCast_add_one_le_iff
  norm_cast

@[simp]

Depends on / 依赖: convert, natCast_add_one_le_iff
-/
lemma two_le_iff_one_lt {c : Cardinal} : 2 <= c ↔ 1 < c := by
  convert! natCast_add_one_le_iff
  norm_cast

@[simp]
/--
theorem `succ_zero` / 定理 `succ_zero`

English:
theorem succ_zero
  statement: succ (0 : Cardinal) = 1
  proof: by norm_cast

中文:
定理 succ_zero
  结论: succ (0 : Cardinal) = 1
  证明: by norm_cast
-/
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast

-- This works generally to prove inequalities between numeric cardinals.
/--
theorem `one_lt_two` / 定理 `one_lt_two`

English:
theorem one_lt_two
  statement: (1 : Cardinal) < 2
  proof: by norm_cast

中文:
定理 one_lt_two
  结论: (1 : Cardinal) < 2
  证明: by norm_cast
-/
theorem one_lt_two : (1 : Cardinal) < 2 := by norm_cast

/--
theorem `exists_finset_eq_card` / 定理 `exists_finset_eq_card`

English:
theorem exists_finset_eq_card
  given: {α} {n : Nat} (h : n <= #α)
  proof: by
  obtain hα | hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩

中文:
定理 exists_finset_eq_card
  条件: {α} {n : 自然数} (h : n <= #α)
  证明: by
  obtain hα | hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩

Depends on / 依赖: Finset, Finset.exists_subset_card_eq, Fintype, Fintype.ofFinite, Infinite, Infinite.exists_subset_card_eq, exists_subset_card_eq, finite_or_infinite, hs.symm, ofFinite
-/
theorem exists_finset_eq_card {α} {n : Nat} (h : n <= #α) :
    exists s : Finset α, n = s.card := by
  obtain hα | hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩

/--
theorem `exists_finset_le_card` / 定理 `exists_finset_le_card`

English:
theorem exists_finset_le_card
  given: (α : Type*) (n : Nat) (h : n <= #α)
  proof: have ⟨s, eq⟩ := exists_finset_eq_card h
  ⟨s, eq.le⟩

中文:
定理 exists_finset_le_card
  条件: (α : 类型) (n : 自然数) (h : n <= #α)
  证明: have ⟨s, eq⟩ := exists_finset_eq_card h
  ⟨s, eq.le⟩

Depends on / 依赖: eq.le, exists_finset_eq_card
-/
theorem exists_finset_le_card (α : Type*) (n : Nat) (h : n <= #α) :
    exists s : Finset α, n <= s.card :=
  have ⟨s, eq⟩ := exists_finset_eq_card h
  ⟨s, eq.le⟩

/--
theorem `card_le_of` / 定理 `card_le_of`

English:
theorem card_le_of
  given: {α : Type u} {n : Nat} (H : forall s : Finset α, s.card <= n)
  statement: #α <= n
  proof: by
  contrapose! H
  apply exists_finset_le_card α (n + 1)
  simpa using H

中文:
定理 card_le_of
  条件: {α : 类型u} {n : 自然数} (H : 对任意 s : Finset α, s.card <= n)
  结论: #α <= n
  证明: by
  contrapose! H
  apply exists_finset_le_card α (n + 1)
  simpa using H

Depends on / 依赖: contrapose, exists_finset_le_card
-/
theorem card_le_of {α : Type u} {n : Nat} (H : forall s : Finset α, s.card <= n) : #α <= n := by
  contrapose! H
  apply exists_finset_le_card α (n + 1)
  simpa using H

/--
theorem `cantor'` / 定理 `cantor'`

English:
theorem cantor'
  given: (a) {b : Cardinal} (hb : 1 < b)
  statement: a < b ^ a
  proof: by
  rw [← succ_le_iff]; rw [(by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)

中文:
定理 cantor'
  条件: (a) {b : Cardinal} (hb : 1 < b)
  结论: a < b ^ a
  证明: by
  rw [← succ_le_iff]; rw [(by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)

Depends on / 依赖: Cardinal, cantor, power_le_power_right, succ_le_iff, trans_le
-/
theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a := by
  rw [← succ_le_iff]; rw [(by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)

/--
theorem `one_le_iff_pos` / 定理 `one_le_iff_pos`

English:
theorem one_le_iff_pos
  given: {c : Cardinal}
  statement: 1 <= c ↔ 0 < c
  proof: by
  rw [← succ_zero]; rw [succ_le_iff]

中文:
定理 one_le_iff_pos
  条件: {c : Cardinal}
  结论: 1 <= c ↔ 0 < c
  证明: by
  rw [← succ_zero]; rw [succ_le_iff]
-/
protected theorem one_le_iff_pos {c : Cardinal} : 1 <= c ↔ 0 < c := by
  rw [← succ_zero]; rw [succ_le_iff]

/--
theorem `one_le_iff_ne_zero` / 定理 `one_le_iff_ne_zero`

English:
theorem one_le_iff_ne_zero
  given: {c : Cardinal}
  statement: 1 <= c ↔ c != 0
  proof: by
  rw [Cardinal.one_le_iff_pos]; rw [pos_iff_ne_zero]

@[simp]

中文:
定理 one_le_iff_ne_zero
  条件: {c : Cardinal}
  结论: 1 <= c ↔ c != 0
  证明: by
  rw [Cardinal.one_le_iff_pos]; rw [pos_iff_ne_zero]

@[simp]
-/
protected theorem one_le_iff_ne_zero {c : Cardinal} : 1 <= c ↔ c != 0 := by
  rw [Cardinal.one_le_iff_pos]; rw [pos_iff_ne_zero]

@[simp]
/--
theorem `lt_one_iff` / 定理 `lt_one_iff`

English:
theorem lt_one_iff
  given: {c : Cardinal}
  statement: c < 1 ↔ c = 0
  proof: by
  simpa using lt_succ_bot_iff (a := c)

@[deprecated (since := "2026-03-24")]
alias lt_one_iff_zero := Cardinal.lt_one_iff

中文:
定理 lt_one_iff
  条件: {c : Cardinal}
  结论: c < 1 ↔ c = 0
  证明: by
  simpa using lt_succ_bot_iff (a := c)

@[deprecated (since := "2026-03-24")]
alias lt_one_iff_zero := Cardinal.lt_one_iff
-/
protected theorem lt_one_iff {c : Cardinal} : c < 1 ↔ c = 0 := by
  simpa using lt_succ_bot_iff (a := c)

@[deprecated (since := "2026-03-24")]
alias lt_one_iff_zero := Cardinal.lt_one_iff

/--
theorem `le_one_iff` / 定理 `le_one_iff`

English:
theorem le_one_iff
  given: {c : Cardinal}
  statement: c <= 1 ↔ c = 0 ∨ c = 1
  proof: by
  simpa using le_succ_bot_iff (a := c)

中文:
定理 le_one_iff
  条件: {c : Cardinal}
  结论: c <= 1 ↔ c = 0 ∨ c = 1
  证明: by
  simpa using le_succ_bot_iff (a := c)
-/
protected theorem le_one_iff {c : Cardinal} : c <= 1 ↔ c = 0 ∨ c = 1 := by
  simpa using le_succ_bot_iff (a := c)


/--
lemma `natCast_lt_aleph0` / 引理 `natCast_lt_aleph0`

English:
lemma natCast_lt_aleph0
  given: {n : Nat}
  statement: (n : Cardinal.{u}) < ℵ₀
  proof: by
  rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one]; rw [← lift_mk_fin]; rw [aleph0]; rw [lift_mk_le.{u}]
  exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩

@[deprecated natCast_lt_aleph0 (since := "2026-01-21")]

中文:
引理 natCast_lt_aleph0
  条件: {n : 自然数}
  结论: (n : Cardinal.{u}) < ℵ₀
  证明: by
  rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one]; rw [← lift_mk_fin]; rw [aleph0]; rw [lift_mk_le.{u}]
  exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩

@[deprecated natCast_lt_aleph0 (since := "2026-01-21")]
-/
@[simp] lemma natCast_lt_aleph0 {n : Nat} : (n : Cardinal.{u}) < ℵ₀ := by
  rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one]; rw [← lift_mk_fin]; rw [aleph0]; rw [lift_mk_le.{u}]
  exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩

@[deprecated natCast_lt_aleph0 (since := "2026-01-21")]
/--
theorem `nat_lt_aleph0` / 定理 `nat_lt_aleph0`

English:
theorem nat_lt_aleph0
  given: (n : Nat)
  statement: (n : Cardinal.{u}) < ℵ₀
  proof: natCast_lt_aleph0

中文:
定理 nat_lt_aleph0
  条件: (n : 自然数)
  结论: (n : Cardinal.{u}) < ℵ₀
  证明: natCast_lt_aleph0

Depends on / 依赖: natCast_lt_aleph0
-/
theorem nat_lt_aleph0 (n : Nat) : (n : Cardinal.{u}) < ℵ₀ := natCast_lt_aleph0

/--
lemma `natCast_le_aleph0` / 引理 `natCast_le_aleph0`

English:
lemma natCast_le_aleph0
  given: {n : Nat}
  statement: (n : Cardinal.{u}) <= ℵ₀
  proof: natCast_lt_aleph0.le

中文:
引理 natCast_le_aleph0
  条件: {n : 自然数}
  结论: (n : Cardinal.{u}) <= ℵ₀
  证明: natCast_lt_aleph0.le
-/
@[simp] lemma natCast_le_aleph0 {n : Nat} : (n : Cardinal.{u}) <= ℵ₀ := natCast_lt_aleph0.le

/--
lemma `ofNat_lt_aleph0` / 引理 `ofNat_lt_aleph0`

English:
lemma ofNat_lt_aleph0
  given: {n : Nat} [n.AtLeastTwo]
  statement: ofNat(n) < ℵ₀
  proof: natCast_lt_aleph0

中文:
引理 ofNat_lt_aleph0
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: of自然数(n) < ℵ₀
  证明: natCast_lt_aleph0
-/
@[simp] lemma ofNat_lt_aleph0 {n : Nat} [n.AtLeastTwo] : ofNat(n) < ℵ₀ := natCast_lt_aleph0
/--
lemma `ofNat_le_aleph0` / 引理 `ofNat_le_aleph0`

English:
lemma ofNat_le_aleph0
  given: {n : Nat} [n.AtLeastTwo]
  statement: ofNat(n) <= ℵ₀
  proof: natCast_le_aleph0

@[simp]

中文:
引理 ofNat_le_aleph0
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: of自然数(n) <= ℵ₀
  证明: natCast_le_aleph0

@[simp]
-/
@[simp] lemma ofNat_le_aleph0 {n : Nat} [n.AtLeastTwo] : ofNat(n) <= ℵ₀ := natCast_le_aleph0

@[simp]
/--
theorem `one_lt_aleph0` / 定理 `one_lt_aleph0`

English:
theorem one_lt_aleph0
  statement: 1 < ℵ₀
  proof: by simpa using natCast_lt_aleph0 (n := 1)

@[simp]

中文:
定理 one_lt_aleph0
  结论: 1 < ℵ₀
  证明: by simpa using natCast_lt_aleph0 (n := 1)

@[simp]

Depends on / 依赖: natCast_lt_aleph0
-/
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using natCast_lt_aleph0 (n := 1)

@[simp]
/--
theorem `one_le_aleph0` / 定理 `one_le_aleph0`

English:
theorem one_le_aleph0
  statement: 1 <= ℵ₀
  proof: one_lt_aleph0.le

中文:
定理 one_le_aleph0
  结论: 1 <= ℵ₀
  证明: one_lt_aleph0.le

Depends on / 依赖: one_lt_aleph0, one_lt_aleph0.le
-/
theorem one_le_aleph0 : 1 <= ℵ₀ :=
  one_lt_aleph0.le

/--
theorem `lt_aleph0` / 定理 `lt_aleph0`

English:
theorem lt_aleph0
  given: {c : Cardinal}
  statement: c < ℵ₀ ↔ exists n : Nat, c = n
  proof: ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, h', rfl⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset Nat using this
      simp
    contrapose! h'
    have := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨_, e⟩ => e.symm ▸ n

中文:
定理 lt_aleph0
  条件: {c : Cardinal}
  结论: c < ℵ₀ ↔ 存在 n : 自然数, c = n
  证明: ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, h', rfl⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset Nat using this
      simp
    contrapose! h'
    have := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨_, e⟩ => e.symm ▸ n

Depends on / 依赖: Finite, Finset, Infinite, Infinite.natEmbedding, Infinite.to_subtype, S.Finite, contrapose, e.symm, le_mk_iff_exists_set, lt_lift_iff, natCast_lt_aleph0, natEmbedding, to_subtype
-/
theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, h', rfl⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset Nat using this
      simp
    contrapose! h'
    have := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨_, e⟩ => e.symm ▸ natCast_lt_aleph0⟩

/--
lemma `succ_eq_of_lt_aleph0` / 引理 `succ_eq_of_lt_aleph0`

English:
lemma succ_eq_of_lt_aleph0
  given: {c : Cardinal} (h : c < ℵ₀)
  statement: Order.succ c = c + 1
  proof: by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn]; rw [succ_natCast]

中文:
引理 succ_eq_of_lt_aleph0
  条件: {c : Cardinal} (h : c < ℵ₀)
  结论: Order.succ c = c + 1
  证明: by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn]; rw [succ_natCast]

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0.mp, lt_aleph0, succ_natCast
-/
lemma succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1 := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn]; rw [succ_natCast]

/--
theorem `aleph0_le` / 定理 `aleph0_le`

English:
theorem aleph0_le
  given: {c : Cardinal}
  statement: ℵ₀ <= c ↔ forall n : Nat, ↑n <= c where
  proof: natCast_le_aleph0.trans h
  mpr h := le_of_not_gt fun hn => by
    rcases lt_aleph0.1 hn with ⟨n, rfl⟩
    exact (Nat.lt_succ_self _).not_ge (Nat.cast_le.1 (h (n + 1)))

中文:
定理 aleph0_le
  条件: {c : Cardinal}
  结论: ℵ₀ <= c ↔ 对任意 n : 自然数, ↑n <= c where
  证明: natCast_le_aleph0.trans h
  mpr h := le_of_not_gt fun hn => by
    rcases lt_aleph0.1 hn with ⟨n, rfl⟩
    exact (Nat.lt_succ_self _).not_ge (Nat.cast_le.1 (h (n + 1)))

Depends on / 依赖: natCast_le_aleph0, natCast_le_aleph0.trans
-/
theorem aleph0_le {c : Cardinal} : ℵ₀ <= c ↔ forall n : Nat, ↑n <= c where
  mp h _ := natCast_le_aleph0.trans h
  mpr h := le_of_not_gt fun hn => by
    rcases lt_aleph0.1 hn with ⟨n, rfl⟩
    exact (Nat.lt_succ_self _).not_ge (Nat.cast_le.1 (h (n + 1)))

/--
theorem `isSuccPrelimit_aleph0` / 定理 `isSuccPrelimit_aleph0`

English:
theorem isSuccPrelimit_aleph0
  statement: IsSuccPrelimit ℵ₀
  proof: isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    apply natCast_lt_aleph0

中文:
定理 isSuccPrelimit_aleph0
  结论: IsSuccPrelimit ℵ₀
  证明: isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    apply natCast_lt_aleph0

Depends on / 依赖: Nat.cast_add_one, cast_add_one, isSuccPrelimit_of_succ_lt, lt_aleph0, natCast_lt_aleph0, succ_natCast
-/
theorem isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀ :=
  isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    apply natCast_lt_aleph0

/--
theorem `isSuccLimit_aleph0` / 定理 `isSuccLimit_aleph0`

English:
theorem isSuccLimit_aleph0
  statement: IsSuccLimit ℵ₀
  proof: by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩

中文:
定理 isSuccLimit_aleph0
  结论: IsSuccLimit ℵ₀
  证明: by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩

Depends on / 依赖: Cardinal, Cardinal.isSuccLimit_iff, aleph0_ne_zero, isSuccLimit_iff, isSuccPrelimit_aleph0
-/
theorem isSuccLimit_aleph0 : IsSuccLimit ℵ₀ := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩

/--
lemma `not_isSuccLimit_natCast` / 引理 `not_isSuccLimit_natCast`

English:
lemma not_isSuccLimit_natCast
  statement: (n : Nat) -> ¬ IsSuccLimit (n : Cardinal.{u})

中文:
引理 not_isSuccLimit_natCast
  结论: (n : 自然数) -> ¬ IsSuccLimit (n : Cardinal.{u})
-/
lemma not_isSuccLimit_natCast : (n : Nat) -> ¬ IsSuccLimit (n : Cardinal.{u})
  | 0, e => e.1 isMin_bot
  | Nat.succ n, h => by
    rw [Nat.cast_succ]; rw [← succ_natCast] at h
    exact Order.not_isSuccLimit_succ _ h

/--
theorem `not_isSuccLimit_of_lt_aleph0` / 定理 `not_isSuccLimit_of_lt_aleph0`

English:
theorem not_isSuccLimit_of_lt_aleph0
  given: {c : Cardinal} (h : c < ℵ₀)
  statement: ¬ IsSuccLimit c
  proof: by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n

中文:
定理 not_isSuccLimit_of_lt_aleph0
  条件: {c : Cardinal} (h : c < ℵ₀)
  结论: ¬ IsSuccLimit c
  证明: by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n

Depends on / 依赖: lt_aleph0, not_isSuccLimit_natCast
-/
theorem not_isSuccLimit_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c := by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n

/--
theorem `aleph0_le_of_isSuccLimit` / 定理 `aleph0_le_of_isSuccLimit`

English:
theorem aleph0_le_of_isSuccLimit
  given: {c : Cardinal} (h : IsSuccLimit c)
  statement: ℵ₀ <= c
  proof: by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h

中文:
定理 aleph0_le_of_isSuccLimit
  条件: {c : Cardinal} (h : IsSuccLimit c)
  结论: ℵ₀ <= c
  证明: by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h

Depends on / 依赖: contrapose, not_isSuccLimit_of_lt_aleph0
-/
theorem aleph0_le_of_isSuccLimit {c : Cardinal} (h : IsSuccLimit c) : ℵ₀ <= c := by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h

/--
theorem `isStrongLimit_aleph0` / 定理 `isStrongLimit_aleph0`

English:
theorem isStrongLimit_aleph0
  statement: IsStrongLimit ℵ₀
  proof: by
  refine ⟨aleph0_ne_zero, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := lt_aleph0.1 hx
  exact mod_cast natCast_lt_aleph0

中文:
定理 isStrongLimit_aleph0
  结论: IsStrongLimit ℵ₀
  证明: by
  refine ⟨aleph0_ne_zero, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := lt_aleph0.1 hx
  exact mod_cast natCast_lt_aleph0

Depends on / 依赖: aleph0_ne_zero, lt_aleph0, mod_cast, natCast_lt_aleph0
-/
theorem isStrongLimit_aleph0 : IsStrongLimit ℵ₀ := by
  refine ⟨aleph0_ne_zero, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := lt_aleph0.1 hx
  exact mod_cast natCast_lt_aleph0

/--
theorem `IsStrongLimit.aleph0_le` / 定理 `IsStrongLimit.aleph0_le`

English:
theorem IsStrongLimit.aleph0_le
  given: {c} (H : IsStrongLimit c)
  statement: ℵ₀ <= c
  proof: aleph0_le_of_isSuccLimit H.isSuccLimit

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]

中文:
定理 IsStrongLimit.aleph0_le
  条件: {c} (H : IsStrongLimit c)
  结论: ℵ₀ <= c
  证明: aleph0_le_of_isSuccLimit H.isSuccLimit

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]

Depends on / 依赖: H.isSuccLimit, aleph0_le_of_isSuccLimit, isSuccLimit
-/
theorem IsStrongLimit.aleph0_le {c} (H : IsStrongLimit c) : ℵ₀ <= c :=
  aleph0_le_of_isSuccLimit H.isSuccLimit

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]
/--
lemma `exists_eq_natCast_of_iSup_eq` / 引理 `exists_eq_natCast_of_iSup_eq`

English:
lemma exists_eq_natCast_of_iSup_eq
  statement: {ι : Type u} [Nonempty ι] (f : ι -> Cardinal.{v})
  proof: by
  rw [← h]
  exact exists_eq_ciSup_of_not_isSuccLimit hf (h ▸ not_isSuccLimit_natCast n)

@[simp]

中文:
引理 exists_eq_natCast_of_iSup_eq
  结论: {ι : 类型u} [Nonempty ι] (f : ι -> Cardinal.{v})
  证明: by
  rw [← h]
  exact exists_eq_ciSup_of_not_isSuccLimit hf (h ▸ not_isSuccLimit_natCast n)

@[simp]

Depends on / 依赖: exists_eq_ciSup_of_not_isSuccLimit, not_isSuccLimit_natCast
-/
lemma exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι -> Cardinal.{v})
    (hf : BddAbove (range f)) (n : Nat) (h : ⨆ i, f i = n) : exists i, f i = n := by
  rw [← h]
  exact exists_eq_ciSup_of_not_isSuccLimit hf (h ▸ not_isSuccLimit_natCast n)

@[simp]
/--
theorem `range_natCast` / 定理 `range_natCast`

English:
theorem range_natCast
  statement: range ((↑) : Nat -> Cardinal) = Iio ℵ₀
  proof: ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

中文:
定理 range_natCast
  结论: range ((↑) : 自然数 -> Cardinal) = Iio ℵ₀
  证明: ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

Depends on / 依赖: eq_comm, lt_aleph0, mem_Iio, mem_range
-/
theorem range_natCast : range ((↑) : Nat -> Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

/--
theorem `mk_eq_nat_iff` / 定理 `mk_eq_nat_iff`

English:
theorem mk_eq_nat_iff
  given: {α : Type u} {n : Nat}
  statement: #α = n ↔ Nonempty (α ≃ Fin n)
  proof: by
  rw [← lift_mk_fin]; rw [← lift_uzero #α]; rw [lift_mk_eq']

中文:
定理 mk_eq_nat_iff
  条件: {α : 类型u} {n : 自然数}
  结论: #α = n ↔ Nonempty (α ≃ Fin n)
  证明: by
  rw [← lift_mk_fin]; rw [← lift_uzero #α]; rw [lift_mk_eq']

Depends on / 依赖: lift_mk_eq, lift_mk_fin, lift_uzero
-/
theorem mk_eq_nat_iff {α : Type u} {n : Nat} : #α = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin]; rw [← lift_uzero #α]; rw [lift_mk_eq']

/--
theorem `lt_aleph0_iff_finite` / 定理 `lt_aleph0_iff_finite`

English:
theorem lt_aleph0_iff_finite
  given: {α : Type u}
  statement: #α < ℵ₀ ↔ Finite α
  proof: by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

中文:
定理 lt_aleph0_iff_finite
  条件: {α : 类型u}
  结论: #α < ℵ₀ ↔ Finite α
  证明: by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

Depends on / 依赖: finite_iff_exists_equiv_fin, lt_aleph0, mk_eq_nat_iff
-/
theorem lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

/--
theorem `lt_aleph0_iff_fintype` / 定理 `lt_aleph0_iff_fintype`

English:
theorem lt_aleph0_iff_fintype
  given: {α : Type u}
  statement: #α < ℵ₀ ↔ Nonempty (Fintype α)
  proof: lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)

中文:
定理 lt_aleph0_iff_fintype
  条件: {α : 类型u}
  结论: #α < ℵ₀ ↔ Nonempty (Fintype α)
  证明: lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)

Depends on / 依赖: finite_iff_nonempty_fintype, lt_aleph0_iff_finite, lt_aleph0_iff_finite.trans
-/
theorem lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)

/--
theorem `lt_aleph0_of_finite` / 定理 `lt_aleph0_of_finite`

English:
theorem lt_aleph0_of_finite
  given: (α : Type u) [Finite α]
  statement: #α < ℵ₀
  proof: lt_aleph0_iff_finite.2 ‹_›

中文:
定理 lt_aleph0_of_finite
  条件: (α : 类型u) [Finite α]
  结论: #α < ℵ₀
  证明: lt_aleph0_iff_finite.2 ‹_›

Depends on / 依赖: lt_aleph0_iff_finite
-/
theorem lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›

/--
theorem `lt_aleph0_iff_set_finite` / 定理 `lt_aleph0_iff_set_finite`

English:
theorem lt_aleph0_iff_set_finite
  given: {S : Set α}
  statement: #S < ℵ₀ ↔ S.Finite
  proof: lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]

中文:
定理 lt_aleph0_iff_set_finite
  条件: {S : Set α}
  结论: #S < ℵ₀ ↔ S.Finite
  证明: lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]

Depends on / 依赖: finite_coe_iff, lt_aleph0_iff_finite, lt_aleph0_iff_finite.trans
-/
theorem lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]
/--
theorem `lt_aleph0_iff_subtype_finite` / 定理 `lt_aleph0_iff_subtype_finite`

English:
theorem lt_aleph0_iff_subtype_finite
  given: {p : α -> Prop}
  statement: #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite
  proof: lt_aleph0_iff_set_finite

中文:
定理 lt_aleph0_iff_subtype_finite
  条件: {p : α -> 命题}
  结论: #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite
  证明: lt_aleph0_iff_set_finite

Depends on / 依赖: lt_aleph0_iff_set_finite
-/
theorem lt_aleph0_iff_subtype_finite {p : α -> Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite

/--
theorem `mk_le_aleph0_iff` / 定理 `mk_le_aleph0_iff`

English:
theorem mk_le_aleph0_iff
  statement: #α <= ℵ₀ ↔ Countable α
  proof: by
  rw [countable_iff_nonempty_embedding]; rw [aleph0]; rw [← lift_uzero #α]; rw [lift_mk_le']

@[simp]

中文:
定理 mk_le_aleph0_iff
  结论: #α <= ℵ₀ ↔ Countable α
  证明: by
  rw [countable_iff_nonempty_embedding]; rw [aleph0]; rw [← lift_uzero #α]; rw [lift_mk_le']

@[simp]

Depends on / 依赖: aleph0, countable_iff_nonempty_embedding, lift_mk_le, lift_uzero
-/
theorem mk_le_aleph0_iff : #α <= ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding]; rw [aleph0]; rw [← lift_uzero #α]; rw [lift_mk_le']

@[simp]
/--
theorem `mk_le_aleph0` / 定理 `mk_le_aleph0`

English:
theorem mk_le_aleph0
  given: [Countable α]
  statement: #α <= ℵ₀
  proof: mk_le_aleph0_iff.mpr ‹_›

中文:
定理 mk_le_aleph0
  条件: [Countable α]
  结论: #α <= ℵ₀
  证明: mk_le_aleph0_iff.mpr ‹_›

Depends on / 依赖: mk_le_aleph0_iff, mk_le_aleph0_iff.mpr
-/
theorem mk_le_aleph0 [Countable α] : #α <= ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›

/--
theorem `le_aleph0_iff_set_countable` / 定理 `le_aleph0_iff_set_countable`

English:
theorem le_aleph0_iff_set_countable
  given: {s : Set α}
  statement: #s <= ℵ₀ ↔ s.Countable
  proof: mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]

中文:
定理 le_aleph0_iff_set_countable
  条件: {s : Set α}
  结论: #s <= ℵ₀ ↔ s.Countable
  证明: mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]

Depends on / 依赖: mk_le_aleph0_iff
-/
theorem le_aleph0_iff_set_countable {s : Set α} : #s <= ℵ₀ ↔ s.Countable := mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]
/--
theorem `le_aleph0_iff_subtype_countable` / 定理 `le_aleph0_iff_subtype_countable`

English:
theorem le_aleph0_iff_subtype_countable
  given: {p : α -> Prop}
  proof: le_aleph0_iff_set_countable

中文:
定理 le_aleph0_iff_subtype_countable
  条件: {p : α -> 命题}
  证明: le_aleph0_iff_set_countable

Depends on / 依赖: le_aleph0_iff_set_countable
-/
theorem le_aleph0_iff_subtype_countable {p : α -> Prop} :
    #{ x // p x } <= ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable

/--
theorem `aleph0_lt_mk_iff` / 定理 `aleph0_lt_mk_iff`

English:
theorem aleph0_lt_mk_iff
  statement: ℵ₀ < #α ↔ Uncountable α
  proof: by
  rw [← not_le]; rw [← not_countable_iff]; rw [not_iff_not]; rw [mk_le_aleph0_iff]

@[simp]

中文:
定理 aleph0_lt_mk_iff
  结论: ℵ₀ < #α ↔ Uncountable α
  证明: by
  rw [← not_le]; rw [← not_countable_iff]; rw [not_iff_not]; rw [mk_le_aleph0_iff]

@[simp]

Depends on / 依赖: mk_le_aleph0_iff, not_countable_iff, not_iff_not, not_le
-/
theorem aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α := by
  rw [← not_le]; rw [← not_countable_iff]; rw [not_iff_not]; rw [mk_le_aleph0_iff]

@[simp]
/--
theorem `aleph0_lt_mk` / 定理 `aleph0_lt_mk`

English:
theorem aleph0_lt_mk
  given: [Uncountable α]
  statement: ℵ₀ < #α
  proof: aleph0_lt_mk_iff.mpr ‹_›

中文:
定理 aleph0_lt_mk
  条件: [Uncountable α]
  结论: ℵ₀ < #α
  证明: aleph0_lt_mk_iff.mpr ‹_›

Depends on / 依赖: aleph0_lt_mk_iff, aleph0_lt_mk_iff.mpr
-/
theorem aleph0_lt_mk [Uncountable α] : ℵ₀ < #α :=
  aleph0_lt_mk_iff.mpr ‹_›

/--
Instance `canLiftCardinalNat` / 实例 `canLiftCardinalNat`

English:
instance canLiftCardinalNat
  signature: : CanLift Cardinal Nat (↑) fun x => x < ℵ₀
  body: ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

中文:
实例 canLiftCardinalNat
  签名: : CanLift Cardinal 自然数 (↑) fun x => x < ℵ₀
  定义体: ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

Depends on / 依赖: hn.symm, lt_aleph0, lt_aleph0.mp
-/
instance canLiftCardinalNat : CanLift Cardinal Nat (↑) fun x => x < ℵ₀ :=
  ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

/--
theorem `add_lt_aleph0` / 定理 `add_lt_aleph0`

English:
theorem add_lt_aleph0
  given: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  statement: a + b < ℵ₀
  proof: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply natCast_lt_aleph0

中文:
定理 add_lt_aleph0
  条件: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  结论: a + b < ℵ₀
  证明: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply natCast_lt_aleph0

Depends on / 依赖: Nat.cast_add, cast_add, lt_aleph0, natCast_lt_aleph0
-/
theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply natCast_lt_aleph0

/--
theorem `add_lt_aleph0_iff` / 定理 `add_lt_aleph0_iff`

English:
theorem add_lt_aleph0_iff
  given: {a b : Cardinal}
  statement: a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
  proof: ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩

中文:
定理 add_lt_aleph0_iff
  条件: {a b : Cardinal}
  结论: a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
  证明: ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩

Depends on / 依赖: add_lt_aleph0, self_le_add_left, self_le_add_right, trans_lt
-/
theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩

/--
theorem `aleph0_le_add_iff` / 定理 `aleph0_le_add_iff`

English:
theorem aleph0_le_add_iff
  given: {a b : Cardinal}
  statement: ℵ₀ <= a + b ↔ ℵ₀ <= a ∨ ℵ₀ <= b
  proof: by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

中文:
定理 aleph0_le_add_iff
  条件: {a b : Cardinal}
  结论: ℵ₀ <= a + b ↔ ℵ₀ <= a ∨ ℵ₀ <= b
  证明: by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

Depends on / 依赖: add_lt_aleph0_iff, not_and_or, not_lt
-/
theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ <= a + b ↔ ℵ₀ <= a ∨ ℵ₀ <= b := by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

/--
theorem `nsmul_lt_aleph0_iff` / 定理 `nsmul_lt_aleph0_iff`

English:
theorem nsmul_lt_aleph0_iff
  given: {a : Cardinal}
  statement: forall {n : Nat}, n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀

中文:
定理 nsmul_lt_aleph0_iff
  条件: {a : Cardinal}
  结论: 对任意 {n : 自然数}, n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀
-/
theorem nsmul_lt_aleph0_iff {a : Cardinal} : forall {n : Nat}, n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀
  | 0 => by simpa using aleph0_pos
  | 1 => by simp
  | n + 2 => by rw [succ_nsmul, add_lt_aleph0_iff, nsmul_lt_aleph0_iff]; simp

/--
theorem `nsmul_lt_aleph0_iff_of_ne_zero` / 定理 `nsmul_lt_aleph0_iff_of_ne_zero`

English:
theorem nsmul_lt_aleph0_iff_of_ne_zero
  given: {n : Nat} {a : Cardinal} (h : n != 0)
  statement: n • a < ℵ₀ ↔ a < ℵ₀
  proof: nsmul_lt_aleph0_iff.trans or_iff_right h

中文:
定理 nsmul_lt_aleph0_iff_of_ne_zero
  条件: {n : 自然数} {a : Cardinal} (h : n != 0)
  结论: n • a < ℵ₀ ↔ a < ℵ₀
  证明: nsmul_lt_aleph0_iff.trans or_iff_right h

Depends on / 依赖: nsmul_lt_aleph0_iff, nsmul_lt_aleph0_iff.trans, or_iff_right
-/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : Nat} {a : Cardinal} (h : n != 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
nsmul_lt_aleph0_iff.trans or_iff_right h

/--
theorem `mul_lt_aleph0` / 定理 `mul_lt_aleph0`

English:
theorem mul_lt_aleph0
  given: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  statement: a * b < ℵ₀
  proof: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply natCast_lt_aleph0

中文:
定理 mul_lt_aleph0
  条件: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  结论: a * b < ℵ₀
  证明: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply natCast_lt_aleph0

Depends on / 依赖: Nat.cast_mul, cast_mul, lt_aleph0, natCast_lt_aleph0
-/
theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply natCast_lt_aleph0

/--
theorem `mul_lt_aleph0_iff` / 定理 `mul_lt_aleph0_iff`

English:
theorem mul_lt_aleph0_iff
  given: {a b : Cardinal}
  statement: a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne]; rw [← Cardinal.one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← o

中文:
定理 mul_lt_aleph0_iff
  条件: {a b : Cardinal}
  结论: a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne]; rw [← Cardinal.one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← o

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, Or.inl, aleph0_pos, le_rfl, mul_le_mul, mul_lt_aleph0, mul_one, mul_zero, one_le_iff_ne_zero, one_mul, trans_lt, zero_mul
-/
theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne]; rw [← Cardinal.one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      exact (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph0, aleph0_pos, zero_mul, mul_zero]

/--
theorem `aleph0_le_mul_iff` / 定理 `aleph0_le_mul_iff`

English:
theorem aleph0_le_mul_iff
  given: {a b : Cardinal}
  statement: ℵ₀ <= a * b ↔ a != 0 ∧ b != 0 ∧ (ℵ₀ <= a ∨ ℵ₀ <= b)
  proof: by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

中文:
定理 aleph0_le_mul_iff
  条件: {a b : Cardinal}
  结论: ℵ₀ <= a * b ↔ a != 0 ∧ b != 0 ∧ (ℵ₀ <= a ∨ ℵ₀ <= b)
  证明: by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

Depends on / 依赖: mul_lt_aleph0_iff, not_and_or, not_lt, not_or
-/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ <= a * b ↔ a != 0 ∧ b != 0 ∧ (ℵ₀ <= a ∨ ℵ₀ <= b) := by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

/--
theorem `aleph0_le_mul_iff'` / 定理 `aleph0_le_mul_iff'`

English:
theorem aleph0_le_mul_iff'
  given: {a b : Cardinal.{u}}
  statement: ℵ₀ <= a * b ↔ a != 0 ∧ ℵ₀ <= b ∨ ℵ₀ <= a ∧ b != 0
  proof: by
  have : forall {a : Cardinal.{u}}, ℵ₀ <= a -> a != 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a != 0)]
  simp only [and_comm, or_comm]

中文:
定理 aleph0_le_mul_iff'
  条件: {a b : Cardinal.{u}}
  结论: ℵ₀ <= a * b ↔ a != 0 ∧ ℵ₀ <= b ∨ ℵ₀ <= a ∧ b != 0
  证明: by
  have : forall {a : Cardinal.{u}}, ℵ₀ <= a -> a != 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a != 0)]
  simp only [and_comm, or_comm]

Depends on / 依赖: Cardinal, aleph0_le_mul_iff, aleph0_ne_zero, and_comm, and_iff_right_of_imp, and_left_comm, and_or_left, ne_bot_of_le_ne_bot, or_comm
-/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ <= a * b ↔ a != 0 ∧ ℵ₀ <= b ∨ ℵ₀ <= a ∧ b != 0 := by
  have : forall {a : Cardinal.{u}}, ℵ₀ <= a -> a != 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a != 0)]
  simp only [and_comm, or_comm]

/--
theorem `mul_lt_aleph0_iff_of_ne_zero` / 定理 `mul_lt_aleph0_iff_of_ne_zero`

English:
theorem mul_lt_aleph0_iff_of_ne_zero
  given: {a b : Cardinal} (ha : a != 0) (hb : b != 0)
  proof: by simp [mul_lt_aleph0_iff, ha, hb]

中文:
定理 mul_lt_aleph0_iff_of_ne_zero
  条件: {a b : Cardinal} (ha : a != 0) (hb : b != 0)
  证明: by simp [mul_lt_aleph0_iff, ha, hb]

Depends on / 依赖: mul_lt_aleph0_iff
-/
theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a != 0) (hb : b != 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph0_iff, ha, hb]

/--
theorem `power_lt_aleph0` / 定理 `power_lt_aleph0`

English:
theorem power_lt_aleph0
  given: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  statement: a ^ b < ℵ₀
  proof: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [power_natCast, ← Nat.cast_pow]; apply natCast_lt_aleph0

中文:
定理 power_lt_aleph0
  条件: {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀)
  结论: a ^ b < ℵ₀
  证明: match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [power_natCast, ← Nat.cast_pow]; apply natCast_lt_aleph0

Depends on / 依赖: Nat.cast_pow, cast_pow, lt_aleph0, natCast_lt_aleph0, power_natCast
-/
theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [power_natCast, ← Nat.cast_pow]; apply natCast_lt_aleph0

/--
theorem `eq_one_iff_unique` / 定理 `eq_one_iff_unique`

English:
theorem eq_one_iff_unique
  given: {α : Type*}
  statement: #α = 1 ↔ Subsingleton α ∧ Nonempty α
  proof: calc
    #α = 1 ↔ #α <= 1 ∧ 1 <= #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (Cardinal.one_le_iff_ne_zero.trans mk_ne_zero_iff)

中文:
定理 eq_one_iff_unique
  条件: {α : 类型}
  结论: #α = 1 ↔ Subsingleton α ∧ Nonempty α
  证明: calc
    #α = 1 ↔ #α <= 1 ∧ 1 <= #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (Cardinal.one_le_iff_ne_zero.trans mk_ne_zero_iff)

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero.trans, Nonempty, Subsingleton, le_antisymm_iff, le_one_iff_subsingleton, le_one_iff_subsingleton.and, mk_ne_zero_iff, one_le_iff_ne_zero
-/
theorem eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    #α = 1 ↔ #α <= 1 ∧ 1 <= #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (Cardinal.one_le_iff_ne_zero.trans mk_ne_zero_iff)

/--
theorem `infinite_iff` / 定理 `infinite_iff`

English:
theorem infinite_iff
  given: {α : Type u}
  statement: Infinite α ↔ ℵ₀ <= #α
  proof: by
  rw [← not_lt]; rw [lt_aleph0_iff_finite]; rw [not_finite_iff_infinite]

中文:
定理 infinite_iff
  条件: {α : 类型u}
  结论: Infinite α ↔ ℵ₀ <= #α
  证明: by
  rw [← not_lt]; rw [lt_aleph0_iff_finite]; rw [not_finite_iff_infinite]

Depends on / 依赖: lt_aleph0_iff_finite, not_finite_iff_infinite, not_lt
-/
theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α := by
  rw [← not_lt]; rw [lt_aleph0_iff_finite]; rw [not_finite_iff_infinite]

/--
lemma `aleph0_le_mk_iff` / 引理 `aleph0_le_mk_iff`

English:
lemma aleph0_le_mk_iff
  statement: ℵ₀ <= #α ↔ Infinite α
  proof: infinite_iff.symm

中文:
引理 aleph0_le_mk_iff
  结论: ℵ₀ <= #α ↔ Infinite α
  证明: infinite_iff.symm

Depends on / 依赖: infinite_iff, infinite_iff.symm
-/
lemma aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α := infinite_iff.symm
/--
lemma `mk_lt_aleph0_iff` / 引理 `mk_lt_aleph0_iff`

English:
lemma mk_lt_aleph0_iff
  statement: #α < ℵ₀ ↔ Finite α
  proof: by simp [← not_le, aleph0_le_mk_iff]

中文:
引理 mk_lt_aleph0_iff
  结论: #α < ℵ₀ ↔ Finite α
  证明: by simp [← not_le, aleph0_le_mk_iff]

Depends on / 依赖: aleph0_le_mk_iff, not_le
-/
lemma mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α := by simp [← not_le, aleph0_le_mk_iff]

/--
lemma `mk_lt_aleph0` / 引理 `mk_lt_aleph0`

English:
lemma mk_lt_aleph0
  given: [Finite α]
  statement: #α < ℵ₀
  proof: mk_lt_aleph0_iff.2 ‹_›

@[simp]

中文:
引理 mk_lt_aleph0
  条件: [Finite α]
  结论: #α < ℵ₀
  证明: mk_lt_aleph0_iff.2 ‹_›

@[simp]
-/
@[simp] lemma mk_lt_aleph0 [Finite α] : #α < ℵ₀ := mk_lt_aleph0_iff.2 ‹_›

@[simp]
/--
theorem `aleph0_le_mk` / 定理 `aleph0_le_mk`

English:
theorem aleph0_le_mk
  given: (α : Type u) [Infinite α]
  statement: ℵ₀ <= #α
  proof: infinite_iff.1 ‹_›

中文:
定理 aleph0_le_mk
  条件: (α : 类型u) [Infinite α]
  结论: ℵ₀ <= #α
  证明: infinite_iff.1 ‹_›

Depends on / 依赖: infinite_iff
-/
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α :=
  infinite_iff.1 ‹_›

/--
theorem `_root_.Infinite.of_cardinalMk_le` / 定理 `_root_.Infinite.of_cardinalMk_le`

English:
theorem _root_.Infinite.of_cardinalMk_le
  given: {α β : Type u} [Infinite α] (h : #α <= #β)
  proof: infinite_iff.2 (aleph0_le_mk α).trans h

@[simp]

中文:
定理 _root_.Infinite.of_cardinalMk_le
  条件: {α β : 类型u} [Infinite α] (h : #α <= #β)
  证明: infinite_iff.2 (aleph0_le_mk α).trans h

@[simp]

Depends on / 依赖: aleph0_le_mk, infinite_iff
-/
theorem _root_.Infinite.of_cardinalMk_le {α β : Type u} [Infinite α] (h : #α <= #β) :
Infinite β := infinite_iff.2 (aleph0_le_mk α).trans h

@[simp]
/--
theorem `mk_eq_aleph0` / 定理 `mk_eq_aleph0`

English:
theorem mk_eq_aleph0
  given: (α : Type*) [Countable α] [Infinite α]
  statement: #α = ℵ₀
  proof: mk_le_aleph0.antisymm aleph0_le_mk _

中文:
定理 mk_eq_aleph0
  条件: (α : 类型) [Countable α] [Infinite α]
  结论: #α = ℵ₀
  证明: mk_le_aleph0.antisymm aleph0_le_mk _

Depends on / 依赖: aleph0_le_mk, antisymm, mk_le_aleph0, mk_le_aleph0.antisymm
-/
theorem mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀ :=
mk_le_aleph0.antisymm aleph0_le_mk _

/--
theorem `denumerable_iff` / 定理 `denumerable_iff`

English:
theorem denumerable_iff
  given: {α : Type u}
  statement: Nonempty (Denumerable α) ↔ #α = ℵ₀
  proof: ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    obtain ⟨f⟩ := Quotient.exact h
exact ⟨Denumerable.mk' f.trans Equiv.ulift⟩⟩

中文:
定理 denumerable_iff
  条件: {α : 类型u}
  结论: Nonempty (Denumerable α) ↔ #α = ℵ₀
  证明: ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    obtain ⟨f⟩ := Quotient.exact h
exact ⟨Denumerable.mk' f.trans Equiv.ulift⟩⟩

Depends on / 依赖: Denumerable, Denumerable.eqv, Denumerable.mk, Equiv.ulift, Equiv.ulift.symm, Quotient, Quotient.exact, f.trans, mk_congr
-/
theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    obtain ⟨f⟩ := Quotient.exact h
exact ⟨Denumerable.mk' f.trans Equiv.ulift⟩⟩

/--
theorem `mk_denumerable` / 定理 `mk_denumerable`

English:
theorem mk_denumerable
  given: (α : Type u) [Denumerable α]
  statement: #α = ℵ₀
  proof: denumerable_iff.1 ⟨‹_›⟩

中文:
定理 mk_denumerable
  条件: (α : 类型u) [Denumerable α]
  结论: #α = ℵ₀
  证明: denumerable_iff.1 ⟨‹_›⟩

Depends on / 依赖: denumerable_iff
-/
theorem mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩

/--
theorem `_root_.Set.countable_infinite_iff_nonempty_denumerable` / 定理 `_root_.Set.countable_infinite_iff_nonempty_denumerable`

English:
theorem _root_.Set.countable_infinite_iff_nonempty_denumerable
  given: {α : Type*} {s : Set α}
  proof: by
  rw [nonempty_denumerable_iff]; rw [← Set.infinite_coe_iff]; rw [countable_coe_iff]

@[simp]

中文:
定理 _root_.Set.countable_infinite_iff_nonempty_denumerable
  条件: {α : 类型} {s : Set α}
  证明: by
  rw [nonempty_denumerable_iff]; rw [← Set.infinite_coe_iff]; rw [countable_coe_iff]

@[simp]

Depends on / 依赖: Set.infinite_coe_iff, countable_coe_iff, infinite_coe_iff, nonempty_denumerable_iff
-/
theorem _root_.Set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) := by
  rw [nonempty_denumerable_iff]; rw [← Set.infinite_coe_iff]; rw [countable_coe_iff]

@[simp]
/--
theorem `aleph0_add_aleph0` / 定理 `aleph0_add_aleph0`

English:
theorem aleph0_add_aleph0
  statement: ℵ₀ + ℵ₀ = ℵ₀
  proof: mk_denumerable _

中文:
定理 aleph0_add_aleph0
  结论: ℵ₀ + ℵ₀ = ℵ₀
  证明: mk_denumerable _

Depends on / 依赖: mk_denumerable
-/
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _

/--
theorem `aleph0_mul_aleph0` / 定理 `aleph0_mul_aleph0`

English:
theorem aleph0_mul_aleph0
  statement: ℵ₀ * ℵ₀ = ℵ₀
  proof: mk_denumerable _

@[simp]

中文:
定理 aleph0_mul_aleph0
  结论: ℵ₀ * ℵ₀ = ℵ₀
  证明: mk_denumerable _

@[simp]

Depends on / 依赖: mk_denumerable
-/
theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _

@[simp]
/--
theorem `nat_mul_aleph0` / 定理 `nat_mul_aleph0`

English:
theorem nat_mul_aleph0
  given: {n : Nat} (hn : n != 0)
  statement: ↑n * ℵ₀ = ℵ₀
  proof: le_antisymm (lift_mk_fin n ▸ mk_le_aleph0)
le_mul_of_one_le_left zero_le by rwa [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]

@[simp]

中文:
定理 nat_mul_aleph0
  条件: {n : 自然数} (hn : n != 0)
  结论: ↑n * ℵ₀ = ℵ₀
  证明: le_antisymm (lift_mk_fin n ▸ mk_le_aleph0)
le_mul_of_one_le_left zero_le by rwa [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]

@[simp]

Depends on / 依赖: Nat.cast_le, Nat.cast_one, Nat.one_le_iff_ne_zero, cast_le, cast_one, le_antisymm, le_mul_of_one_le_left, lift_mk_fin, mk_le_aleph0, one_le_iff_ne_zero, zero_le
-/
theorem nat_mul_aleph0 {n : Nat} (hn : n != 0) : ↑n * ℵ₀ = ℵ₀ :=
le_antisymm (lift_mk_fin n ▸ mk_le_aleph0)
le_mul_of_one_le_left zero_le by rwa [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]

@[simp]
/--
theorem `aleph0_mul_nat` / 定理 `aleph0_mul_nat`

English:
theorem aleph0_mul_nat
  given: {n : Nat} (hn : n != 0)
  statement: ℵ₀ * n = ℵ₀
  proof: by rw [mul_comm, nat_mul_aleph0 hn]

@[simp]

中文:
定理 aleph0_mul_nat
  条件: {n : 自然数} (hn : n != 0)
  结论: ℵ₀ * n = ℵ₀
  证明: by rw [mul_comm, nat_mul_aleph0 hn]

@[simp]

Depends on / 依赖: mul_comm, nat_mul_aleph0
-/
theorem aleph0_mul_nat {n : Nat} (hn : n != 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph0 hn]

@[simp]
/--
theorem `ofNat_mul_aleph0` / 定理 `ofNat_mul_aleph0`

English:
theorem ofNat_mul_aleph0
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) * ℵ₀ = ℵ₀
  proof: nat_mul_aleph0 (NeZero.ne n)

@[simp]

中文:
定理 ofNat_mul_aleph0
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) * ℵ₀ = ℵ₀
  证明: nat_mul_aleph0 (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, nat_mul_aleph0
-/
theorem ofNat_mul_aleph0 {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) * ℵ₀ = ℵ₀ :=
  nat_mul_aleph0 (NeZero.ne n)

@[simp]
/--
theorem `aleph0_mul_ofNat` / 定理 `aleph0_mul_ofNat`

English:
theorem aleph0_mul_ofNat
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ℵ₀ * ofNat(n) = ℵ₀
  proof: aleph0_mul_nat (NeZero.ne n)

@[simp]

中文:
定理 aleph0_mul_ofNat
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: ℵ₀ * of自然数(n) = ℵ₀
  证明: aleph0_mul_nat (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, aleph0_mul_nat
-/
theorem aleph0_mul_ofNat {n : Nat} [Nat.AtLeastTwo n] : ℵ₀ * ofNat(n) = ℵ₀ :=
  aleph0_mul_nat (NeZero.ne n)

@[simp]
/--
theorem `add_le_aleph0` / 定理 `add_le_aleph0`

English:
theorem add_le_aleph0
  given: {c₁ c₂ : Cardinal}
  statement: c₁ + c₂ <= ℵ₀ ↔ c₁ <= ℵ₀ ∧ c₂ <= ℵ₀
  proof: ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]

中文:
定理 add_le_aleph0
  条件: {c₁ c₂ : Cardinal}
  结论: c₁ + c₂ <= ℵ₀ ↔ c₁ <= ℵ₀ ∧ c₂ <= ℵ₀
  证明: ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]

Depends on / 依赖: add_le_add, aleph0_add_aleph0, le_add_self, le_add_self.trans, le_self_add, le_self_add.trans
-/
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ <= ℵ₀ ↔ c₁ <= ℵ₀ ∧ c₂ <= ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]
/--
theorem `aleph0_add_nat` / 定理 `aleph0_add_nat`

English:
theorem aleph0_add_nat
  given: (n : Nat)
  statement: ℵ₀ + n = ℵ₀
  proof: (add_le_aleph0.2 ⟨le_rfl, natCast_le_aleph0⟩).antisymm le_self_add

@[simp]

中文:
定理 aleph0_add_nat
  条件: (n : 自然数)
  结论: ℵ₀ + n = ℵ₀
  证明: (add_le_aleph0.2 ⟨le_rfl, natCast_le_aleph0⟩).antisymm le_self_add

@[simp]

Depends on / 依赖: add_le_aleph0, antisymm, le_rfl, le_self_add, natCast_le_aleph0
-/
theorem aleph0_add_nat (n : Nat) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, natCast_le_aleph0⟩).antisymm le_self_add

@[simp]
/--
theorem `nat_add_aleph0` / 定理 `nat_add_aleph0`

English:
theorem nat_add_aleph0
  given: (n : Nat)
  statement: ↑n + ℵ₀ = ℵ₀
  proof: by rw [add_comm, aleph0_add_nat]

@[simp]

中文:
定理 nat_add_aleph0
  条件: (n : 自然数)
  结论: ↑n + ℵ₀ = ℵ₀
  证明: by rw [add_comm, aleph0_add_nat]

@[simp]

Depends on / 依赖: add_comm, aleph0_add_nat
-/
theorem nat_add_aleph0 (n : Nat) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_nat]

@[simp]
/--
theorem `ofNat_add_aleph0` / 定理 `ofNat_add_aleph0`

English:
theorem ofNat_add_aleph0
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) + ℵ₀ = ℵ₀
  proof: nat_add_aleph0 n

@[simp]

中文:
定理 ofNat_add_aleph0
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) + ℵ₀ = ℵ₀
  证明: nat_add_aleph0 n

@[simp]

Depends on / 依赖: nat_add_aleph0
-/
theorem ofNat_add_aleph0 {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) + ℵ₀ = ℵ₀ :=
  nat_add_aleph0 n

@[simp]
/--
theorem `aleph0_add_ofNat` / 定理 `aleph0_add_ofNat`

English:
theorem aleph0_add_ofNat
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ℵ₀ + ofNat(n) = ℵ₀
  proof: aleph0_add_nat n

中文:
定理 aleph0_add_ofNat
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: ℵ₀ + of自然数(n) = ℵ₀
  证明: aleph0_add_nat n

Depends on / 依赖: aleph0_add_nat
-/
theorem aleph0_add_ofNat {n : Nat} [Nat.AtLeastTwo n] : ℵ₀ + ofNat(n) = ℵ₀ :=
  aleph0_add_nat n

/--
theorem `exists_nat_eq_of_le_nat` / 定理 `exists_nat_eq_of_le_nat`

English:
theorem exists_nat_eq_of_le_nat
  given: {c : Cardinal} {n : Nat} (h : c <= n)
  statement: exists m, m <= n ∧ c = m
  proof: by
  lift c to Nat using h.trans_lt natCast_lt_aleph0
  exact ⟨c, mod_cast h, rfl⟩

中文:
定理 exists_nat_eq_of_le_nat
  条件: {c : Cardinal} {n : 自然数} (h : c <= n)
  结论: 存在 m, m <= n ∧ c = m
  证明: by
  lift c to Nat using h.trans_lt natCast_lt_aleph0
  exact ⟨c, mod_cast h, rfl⟩

Depends on / 依赖: h.trans_lt, mod_cast, natCast_lt_aleph0, trans_lt
-/
theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : Nat} (h : c <= n) : exists m, m <= n ∧ c = m := by
  lift c to Nat using h.trans_lt natCast_lt_aleph0
  exact ⟨c, mod_cast h, rfl⟩

/--
theorem `mk_int` / 定理 `mk_int`

English:
theorem mk_int
  statement: #Int = ℵ₀
  proof: mk_denumerable Int

中文:
定理 mk_int
  结论: #整数 = ℵ₀
  证明: mk_denumerable Int

Depends on / 依赖: mk_denumerable
-/
theorem mk_int : #Int = ℵ₀ :=
  mk_denumerable Int

/--
theorem `mk_pnat` / 定理 `mk_pnat`

English:
theorem mk_pnat
  statement: #Nat+ = ℵ₀
  proof: mk_denumerable Nat+

中文:
定理 mk_pnat
  结论: #自然数+ = ℵ₀
  证明: mk_denumerable Nat+

Depends on / 依赖: mk_denumerable
-/
theorem mk_pnat : #Nat+ = ℵ₀ :=
  mk_denumerable Nat+


/--
theorem `mk_additive` / 定理 `mk_additive`

English:
theorem mk_additive
  statement: #(Additive α) = #α
  proof: rfl

中文:
定理 mk_additive
  结论: #(Additive α) = #α
  证明: rfl
-/
@[simp] theorem mk_additive : #(Additive α) = #α := rfl

/--
theorem `mk_multiplicative` / 定理 `mk_multiplicative`

English:
theorem mk_multiplicative
  statement: #(Multiplicative α) = #α
  proof: rfl

中文:
定理 mk_multiplicative
  结论: #(Multiplicative α) = #α
  证明: rfl
-/
@[simp] theorem mk_multiplicative : #(Multiplicative α) = #α := rfl

/--
theorem `mk_mulOpposite` / 定理 `mk_mulOpposite`

English:
theorem mk_mulOpposite
  statement: #(MulOpposite α) = #α
  proof: mk_congr MulOpposite.opEquiv.symm

中文:
定理 mk_mulOpposite
  结论: #(MulOpposite α) = #α
  证明: mk_congr MulOpposite.opEquiv.symm
-/
@[to_additive (attr := simp)] theorem mk_mulOpposite : #(MulOpposite α) = #α :=
  mk_congr MulOpposite.opEquiv.symm

/--
theorem `mk_singleton` / 定理 `mk_singleton`

English:
theorem mk_singleton
  given: {α : Type u} (x : α)
  statement: #({x} : Set α) = 1
  proof: mk_eq_one _

@[simp]

中文:
定理 mk_singleton
  条件: {α : 类型u} (x : α)
  结论: #({x} : Set α) = 1
  证明: mk_eq_one _

@[simp]

Depends on / 依赖: mk_eq_one
-/
theorem mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1 :=
  mk_eq_one _

@[simp]
/--
theorem `mk_vector` / 定理 `mk_vector`

English:
theorem mk_vector
  given: (α : Type u) (n : Nat)
  statement: #(List.Vector α n) = #α ^ n
  proof: (mk_congr (Equiv.vectorEquivFin α n)).trans by simp

中文:
定理 mk_vector
  条件: (α : 类型u) (n : 自然数)
  结论: #(List.Vector α n) = #α ^ n
  证明: (mk_congr (Equiv.vectorEquivFin α n)).trans by simp

Depends on / 依赖: Equiv.vectorEquivFin, mk_congr, vectorEquivFin
-/
theorem mk_vector (α : Type u) (n : Nat) : #(List.Vector α n) = #α ^ n :=
(mk_congr (Equiv.vectorEquivFin α n)).trans by simp

/--
theorem `mk_list_eq_sum_pow` / 定理 `mk_list_eq_sum_pow`

English:
theorem mk_list_eq_sum_pow
  given: (α : Type u)
  statement: #(List α) = sum fun n => #α ^ n
  proof: calc
    #(List α) = #(Σ n, List.Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n => #α ^ n := by simp

中文:
定理 mk_list_eq_sum_pow
  条件: (α : 类型u)
  结论: #(List α) = sum fun n => #α ^ n
  证明: calc
    #(List α) = #(Σ n, List.Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n => #α ^ n := by simp

Depends on / 依赖: Equiv.sigmaFiberEquiv, List.Vector, List.length, Vector, length, mk_congr, sigmaFiberEquiv
-/
theorem mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n => #α ^ n :=
  calc
    #(List α) = #(Σ n, List.Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n => #α ^ n := by simp

/--
theorem `sum_zero_pow` / 定理 `sum_zero_pow`

English:
theorem sum_zero_pow
  statement: sum (fun n => (0 : Cardinal) ^ n) = 1
  proof: by
  rw [← mk_eq_zero (α := PEmpty)]; rw [← mk_list_eq_sum_pow]; rw [mk_eq_one]

中文:
定理 sum_zero_pow
  结论: sum (fun n => (0 : Cardinal) ^ n) = 1
  证明: by
  rw [← mk_eq_zero (α := PEmpty)]; rw [← mk_list_eq_sum_pow]; rw [mk_eq_one]

Depends on / 依赖: PEmpty, mk_eq_one, mk_eq_zero, mk_list_eq_sum_pow
-/
theorem sum_zero_pow : sum (fun n => (0 : Cardinal) ^ n) = 1 := by
  rw [← mk_eq_zero (α := PEmpty)]; rw [← mk_list_eq_sum_pow]; rw [mk_eq_one]

/--
theorem `mk_quot_le` / 定理 `mk_quot_le`

English:
theorem mk_quot_le
  given: {α : Type u} {r : α -> α -> Prop}
  statement: #(Quot r) <= #α
  proof: mk_le_of_surjective Quot.exists_rep

中文:
定理 mk_quot_le
  条件: {α : 类型u} {r : α -> α -> 命题}
  结论: #(Quot r) <= #α
  证明: mk_le_of_surjective Quot.exists_rep

Depends on / 依赖: Quot.exists_rep, exists_rep, mk_le_of_surjective
-/
theorem mk_quot_le {α : Type u} {r : α -> α -> Prop} : #(Quot r) <= #α :=
  mk_le_of_surjective Quot.exists_rep

/--
theorem `mk_quotient_le` / 定理 `mk_quotient_le`

English:
theorem mk_quotient_le
  given: {α : Type u} {s : Setoid α}
  statement: #(Quotient s) <= #α
  proof: mk_quot_le

中文:
定理 mk_quotient_le
  条件: {α : 类型u} {s : Setoid α}
  结论: #(Quotient s) <= #α
  证明: mk_quot_le

Depends on / 依赖: mk_quot_le
-/
theorem mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) <= #α :=
  mk_quot_le

/--
theorem `mk_subtype_le_of_subset` / 定理 `mk_subtype_le_of_subset`

English:
theorem mk_subtype_le_of_subset
  given: {α : Type u} {p q : α -> Prop} (h : forall ⦃x⦄, p x -> q x)
  proof: ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

中文:
定理 mk_subtype_le_of_subset
  条件: {α : 类型u} {p q : α -> 命题} (h : 对任意 ⦃x⦄, p x -> q x)
  证明: ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

Depends on / 依赖: Embedding, Embedding.refl, Embedding.subtypeMap, subtypeMap
-/
theorem mk_subtype_le_of_subset {α : Type u} {p q : α -> Prop} (h : forall ⦃x⦄, p x -> q x) :
    #(Subtype p) <= #(Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

/--
theorem `mk_le_mk_of_subset` / 定理 `mk_le_mk_of_subset`

English:
theorem mk_le_mk_of_subset
  given: {α} {s t : Set α} (h : s subseteq t)
  statement: #s <= #t
  proof: ⟨Set.embeddingOfSubset s t h⟩

中文:
定理 mk_le_mk_of_subset
  条件: {α} {s t : Set α} (h : s subseteq t)
  结论: #s <= #t
  证明: ⟨Set.embeddingOfSubset s t h⟩

Depends on / 依赖: Set.embeddingOfSubset, embeddingOfSubset
-/
theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s subseteq t) : #s <= #t :=
  ⟨Set.embeddingOfSubset s t h⟩

/--
theorem `mk_monotone` / 定理 `mk_monotone`

English:
theorem mk_monotone
  statement: Monotone (α := Set α) (mk ∘ (↑))
  proof: fun _ _ => mk_le_mk_of_subset

@[deprecated mk_eq_zero (since := "2026-01-31")]

中文:
定理 mk_monotone
  结论: Monotone (α := Set α) (mk ∘ (↑))
  证明: fun _ _ => mk_le_mk_of_subset

@[deprecated mk_eq_zero (since := "2026-01-31")]
-/
theorem mk_monotone : Monotone (α := Set α) (mk ∘ (↑)) :=
  fun _ _ => mk_le_mk_of_subset

@[deprecated mk_eq_zero (since := "2026-01-31")]
/--
theorem `mk_emptyCollection` / 定理 `mk_emptyCollection`

English:
theorem mk_emptyCollection
  given: (α : Type u)
  statement: #(∅ : Set α) = 0
  proof: mk_eq_zero _

中文:
定理 mk_emptyCollection
  条件: (α : 类型u)
  结论: #(∅ : Set α) = 0
  证明: mk_eq_zero _

Depends on / 依赖: mk_eq_zero
-/
theorem mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0 :=
  mk_eq_zero _

/--
theorem `mk_set_eq_zero_iff` / 定理 `mk_set_eq_zero_iff`

English:
theorem mk_set_eq_zero_iff
  given: {s : Set α}
  statement: #s = 0 ↔ s = ∅
  proof: by
  rw [mk_eq_zero_iff]; rw [isEmpty_coe_sort]

@[deprecated (since := "2026-01-31")]
alias mk_emptyCollection_iff := mk_set_eq_zero_iff

中文:
定理 mk_set_eq_zero_iff
  条件: {s : Set α}
  结论: #s = 0 ↔ s = ∅
  证明: by
  rw [mk_eq_zero_iff]; rw [isEmpty_coe_sort]

@[deprecated (since := "2026-01-31")]
alias mk_emptyCollection_iff := mk_set_eq_zero_iff

Depends on / 依赖: isEmpty_coe_sort, mk_eq_zero_iff
-/
theorem mk_set_eq_zero_iff {s : Set α} : #s = 0 ↔ s = ∅ := by
  rw [mk_eq_zero_iff]; rw [isEmpty_coe_sort]

@[deprecated (since := "2026-01-31")]
alias mk_emptyCollection_iff := mk_set_eq_zero_iff

/--
theorem `mk_set_ne_zero_iff` / 定理 `mk_set_ne_zero_iff`

English:
theorem mk_set_ne_zero_iff
  given: {s : Set α}
  statement: #s != 0 ↔ s.Nonempty
  proof: by
  rw [mk_ne_zero_iff]; rw [nonempty_coe_sort]

@[simp]

中文:
定理 mk_set_ne_zero_iff
  条件: {s : Set α}
  结论: #s != 0 ↔ s.Nonempty
  证明: by
  rw [mk_ne_zero_iff]; rw [nonempty_coe_sort]

@[simp]

Depends on / 依赖: mk_ne_zero_iff, nonempty_coe_sort
-/
theorem mk_set_ne_zero_iff {s : Set α} : #s != 0 ↔ s.Nonempty := by
  rw [mk_ne_zero_iff]; rw [nonempty_coe_sort]

@[simp]
/--
theorem `mk_univ` / 定理 `mk_univ`

English:
theorem mk_univ
  given: {α : Type u}
  statement: #(@univ α) = #α
  proof: mk_congr (Equiv.Set.univ α)

中文:
定理 mk_univ
  条件: {α : 类型u}
  结论: #(@univ α) = #α
  证明: mk_congr (Equiv.Set.univ α)

Depends on / 依赖: Equiv.Set.univ, mk_congr
-/
theorem mk_univ {α : Type u} : #(@univ α) = #α :=
  mk_congr (Equiv.Set.univ α)

/--
lemma `mk_setProd` / 引理 `mk_setProd`

English:
lemma mk_setProd
  given: {α β : Type u} (s : Set α) (t : Set β)
  statement: #(s ×ˢ t) = #s * #t
  proof: by
  rw [mul_def]; rw [mk_congr (Equiv.Set.prod ..)]

中文:
引理 mk_setProd
  条件: {α β : 类型u} (s : Set α) (t : Set β)
  结论: #(s ×ˢ t) = #s * #t
  证明: by
  rw [mul_def]; rw [mk_congr (Equiv.Set.prod ..)]
-/
@[simp] lemma mk_setProd {α β : Type u} (s : Set α) (t : Set β) : #(s ×ˢ t) = #s * #t := by
  rw [mul_def]; rw [mk_congr (Equiv.Set.prod ..)]

/--
theorem `mk_image_le` / 定理 `mk_image_le`

English:
theorem mk_image_le
  given: {α β : Type u} {f : α -> β} {s : Set α}
  statement: #(f '' s) <= #s
  proof: mk_le_of_surjective imageFactorization_surjective

中文:
定理 mk_image_le
  条件: {α β : 类型u} {f : α -> β} {s : Set α}
  结论: #(f '' s) <= #s
  证明: mk_le_of_surjective imageFactorization_surjective

Depends on / 依赖: imageFactorization_surjective, mk_le_of_surjective
-/
theorem mk_image_le {α β : Type u} {f : α -> β} {s : Set α} : #(f '' s) <= #s :=
  mk_le_of_surjective imageFactorization_surjective

/--
lemma `mk_image2_le` / 引理 `mk_image2_le`

English:
lemma mk_image2_le
  given: {α β γ : Type u} {f : α -> β -> γ} {s : Set α} {t : Set β}
  proof: by
  rw [← image_uncurry_prod]; rw [← mk_setProd]
  exact mk_image_le

中文:
引理 mk_image2_le
  条件: {α β γ : 类型u} {f : α -> β -> γ} {s : Set α} {t : Set β}
  证明: by
  rw [← image_uncurry_prod]; rw [← mk_setProd]
  exact mk_image_le

Depends on / 依赖: image_uncurry_prod, mk_image_le, mk_setProd
-/
lemma mk_image2_le {α β γ : Type u} {f : α -> β -> γ} {s : Set α} {t : Set β} :
    #(image2 f s t) <= #s * #t := by
  rw [← image_uncurry_prod]; rw [← mk_setProd]
  exact mk_image_le

/--
theorem `mk_image_le_lift` / 定理 `mk_image_le_lift`

English:
theorem mk_image_le_lift
  given: {α : Type u} {β : Type v} {f : α -> β} {s : Set α}
  proof: lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ imageFactorization_surjective⟩

中文:
定理 mk_image_le_lift
  条件: {α : 类型u} {β : 类型v} {f : α -> β} {s : Set α}
  证明: lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ imageFactorization_surjective⟩

Depends on / 依赖: Embedding, Embedding.ofSurjective, imageFactorization_surjective, lift_mk_le, ofSurjective
-/
theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α -> β} {s : Set α} :
    lift.{u} #(f '' s) <= lift.{v} #s :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ imageFactorization_surjective⟩

/--
theorem `mk_range_le` / 定理 `mk_range_le`

English:
theorem mk_range_le
  given: {α β : Type u} {f : α -> β}
  statement: #(range f) <= #α
  proof: mk_le_of_surjective rangeFactorization_surjective

中文:
定理 mk_range_le
  条件: {α β : 类型u} {f : α -> β}
  结论: #(range f) <= #α
  证明: mk_le_of_surjective rangeFactorization_surjective

Depends on / 依赖: mk_le_of_surjective, rangeFactorization_surjective
-/
theorem mk_range_le {α β : Type u} {f : α -> β} : #(range f) <= #α :=
  mk_le_of_surjective rangeFactorization_surjective

/--
theorem `mk_range_le_lift` / 定理 `mk_range_le_lift`

English:
theorem mk_range_le_lift
  given: {α : Type u} {β : Type v} {f : α -> β}
  proof: lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ rangeFactorization_surjective⟩

中文:
定理 mk_range_le_lift
  条件: {α : 类型u} {β : 类型v} {f : α -> β}
  证明: lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ rangeFactorization_surjective⟩

Depends on / 依赖: Embedding, Embedding.ofSurjective, lift_mk_le, ofSurjective, rangeFactorization_surjective
-/
theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α -> β} :
    lift.{u} #(range f) <= lift.{v} #α :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ rangeFactorization_surjective⟩

/--
theorem `mk_range_eq` / 定理 `mk_range_eq`

English:
theorem mk_range_eq
  given: (f : α -> β) (h : Injective f)
  statement: #(range f) = #α
  proof: mk_congr (Equiv.ofInjective f h).symm

中文:
定理 mk_range_eq
  条件: (f : α -> β) (h : Injective f)
  结论: #(range f) = #α
  证明: mk_congr (Equiv.ofInjective f h).symm

Depends on / 依赖: Equiv.ofInjective, mk_congr, ofInjective
-/
theorem mk_range_eq (f : α -> β) (h : Injective f) : #(range f) = #α :=
  mk_congr (Equiv.ofInjective f h).symm

/--
theorem `mk_range_eq_of_injective` / 定理 `mk_range_eq_of_injective`

English:
theorem mk_range_eq_of_injective
  given: {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f)
  proof: lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

@[deprecated mk_range_eq_of_injective (since := "2026-01-06")]

中文:
定理 mk_range_eq_of_injective
  条件: {α : 类型u} {β : 类型v} {f : α -> β} (hf : Injective f)
  证明: lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

@[deprecated mk_range_eq_of_injective (since := "2026-01-06")]

Depends on / 依赖: Equiv.ofInjective, lift_mk_eq, ofInjective
-/
theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) :
    lift.{u} #(range f) = lift.{v} #α :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

@[deprecated mk_range_eq_of_injective (since := "2026-01-06")]
/--
theorem `mk_range_eq_lift` / 定理 `mk_range_eq_lift`

English:
theorem mk_range_eq_lift
  given: {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f)
  proof: lift_mk_eq.{v, u, w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩

中文:
定理 mk_range_eq_lift
  条件: {α : 类型u} {β : 类型v} {f : α -> β} (hf : Injective f)
  证明: lift_mk_eq.{v, u, w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩

Depends on / 依赖: Equiv.ofInjective, lift_mk_eq, ofInjective
-/
theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) :
    lift.{max u w} #(range f) = lift.{max v w} #α :=
  lift_mk_eq.{v, u, w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩

/--
lemma `lift_mk_le_lift_mk_of_injective` / 引理 `lift_mk_le_lift_mk_of_injective`

English:
lemma lift_mk_le_lift_mk_of_injective
  given: {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f)
  proof: by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)

中文:
引理 lift_mk_le_lift_mk_of_injective
  条件: {α : 类型u} {β : 类型v} {f : α -> β} (hf : Injective f)
  证明: by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.mk_range_eq_of_injective, Cardinal.mk_set_le, lift_le, mk_range_eq_of_injective, mk_set_le
-/
lemma lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) :
    Cardinal.lift.{v} (#α) <= Cardinal.lift.{u} (#β) := by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)

/--
lemma `lift_mk_le_lift_mk_of_surjective` / 引理 `lift_mk_le_lift_mk_of_surjective`

English:
lemma lift_mk_le_lift_mk_of_surjective
  given: {α : Type u} {β : Type v} {f : α -> β} (hf : Surjective f)
  proof: lift_mk_le_lift_mk_of_injective (injective_surjInv hf)

中文:
引理 lift_mk_le_lift_mk_of_surjective
  条件: {α : 类型u} {β : 类型v} {f : α -> β} (hf : Surjective f)
  证明: lift_mk_le_lift_mk_of_injective (injective_surjInv hf)

Depends on / 依赖: injective_surjInv, lift_mk_le_lift_mk_of_injective
-/
lemma lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α -> β} (hf : Surjective f) :
    Cardinal.lift.{u} (#β) <= Cardinal.lift.{v} (#α) :=
  lift_mk_le_lift_mk_of_injective (injective_surjInv hf)

/--
theorem `mk_image_eq_of_injOn` / 定理 `mk_image_eq_of_injOn`

English:
theorem mk_image_eq_of_injOn
  given: {α β : Type u} (f : α -> β) (s : Set α) (h : InjOn f s)
  proof: mk_congr (Equiv.Set.imageOfInjOn f s h).symm

中文:
定理 mk_image_eq_of_injOn
  条件: {α β : 类型u} (f : α -> β) (s : Set α) (h : InjOn f s)
  证明: mk_congr (Equiv.Set.imageOfInjOn f s h).symm

Depends on / 依赖: AddMonoidHom, Equiv.Set.imageOfInjOn, Function, Function.LeftInverse.map_tsum, LeftInverse, _blockDiagonal, blockDiag, blockDiagonal, continuous_id, continuous_id.matrix_blockDiag, continuous_id.matrix_blockDiagonal, imageOfInjOn, map_tsum, matrix_blockDiag, matrix_blockDiagonal, mk_congr
-/
theorem mk_image_eq_of_injOn {α β : Type u} (f : α -> β) (s : Set α) (h : InjOn f s) :
    #(f '' s) = #s :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm

/--
theorem `mk_image_eq_of_injOn_lift` / 定理 `mk_image_eq_of_injOn_lift`

English:
theorem mk_image_eq_of_injOn_lift
  statement: {α : Type u} {β : Type v} (f : α -> β) (s : Set α)
  proof: lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩

中文:
定理 mk_image_eq_of_injOn_lift
  结论: {α : 类型u} {β : 类型v} (f : α -> β) (s : Set α)
  证明: lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩

Depends on / 依赖: Equiv.Set.imageOfInjOn, imageOfInjOn, lift_mk_eq
-/
theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set α)
    (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩

/--
theorem `mk_image_eq` / 定理 `mk_image_eq`

English:
theorem mk_image_eq
  given: {α β : Type u} {f : α -> β} {s : Set α} (hf : Injective f)
  statement: #(f '' s) = #s
  proof: mk_image_eq_of_injOn _ _ hf.injOn

中文:
定理 mk_image_eq
  条件: {α β : 类型u} {f : α -> β} {s : Set α} (hf : Injective f)
  结论: #(f '' s) = #s
  证明: mk_image_eq_of_injOn _ _ hf.injOn

Depends on / 依赖: hf.injOn, mk_image_eq_of_injOn
-/
theorem mk_image_eq {α β : Type u} {f : α -> β} {s : Set α} (hf : Injective f) : #(f '' s) = #s :=
  mk_image_eq_of_injOn _ _ hf.injOn

/--
theorem `mk_image_eq_lift` / 定理 `mk_image_eq_lift`

English:
theorem mk_image_eq_lift
  given: {α : Type u} {β : Type v} (f : α -> β) (s : Set α) (h : Injective f)
  proof: mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]

中文:
定理 mk_image_eq_lift
  条件: {α : 类型u} {β : 类型v} (f : α -> β) (s : Set α) (h : Injective f)
  证明: mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]

Depends on / 依赖: h.injOn, mk_image_eq_of_injOn_lift
-/
theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set α) (h : Injective f) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]
/--
theorem `mk_image_embedding_lift` / 定理 `mk_image_embedding_lift`

English:
theorem mk_image_embedding_lift
  given: {β : Type v} (f : α ↪ β) (s : Set α)
  proof: mk_image_eq_lift _ _ f.injective

@[simp]

中文:
定理 mk_image_embedding_lift
  条件: {β : 类型v} (f : α ↪ β) (s : Set α)
  证明: mk_image_eq_lift _ _ f.injective

@[simp]

Depends on / 依赖: f.injective, injective, mk_image_eq_lift
-/
theorem mk_image_embedding_lift {β : Type v} (f : α ↪ β) (s : Set α) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_lift _ _ f.injective

@[simp]
/--
theorem `mk_image_embedding` / 定理 `mk_image_embedding`

English:
theorem mk_image_embedding
  given: (f : α ↪ β) (s : Set α)
  statement: #(f '' s) = #s
  proof: by
  simpa using mk_image_embedding_lift f s

中文:
定理 mk_image_embedding
  条件: (f : α ↪ β) (s : Set α)
  结论: #(f '' s) = #s
  证明: by
  simpa using mk_image_embedding_lift f s

Depends on / 依赖: mk_image_embedding_lift
-/
theorem mk_image_embedding (f : α ↪ β) (s : Set α) : #(f '' s) = #s := by
  simpa using mk_image_embedding_lift f s

/--
theorem `iSup_mk_le_mk_iUnion` / 定理 `iSup_mk_le_mk_iUnion`

English:
theorem iSup_mk_le_mk_iUnion
  given: {α : Type u} {ι : Type v} {f : ι -> Set α}
  proof: ciSup_le' fun _ => mk_le_mk_of_subset (subset_iUnion _ _)

中文:
定理 iSup_mk_le_mk_iUnion
  条件: {α : 类型u} {ι : 类型v} {f : ι -> Set α}
  证明: ciSup_le' fun _ => mk_le_mk_of_subset (subset_iUnion _ _)

Depends on / 依赖: ciSup_le, mk_le_mk_of_subset, subset_iUnion
-/
theorem iSup_mk_le_mk_iUnion {α : Type u} {ι : Type v} {f : ι -> Set α} :
    ⨆ i, #(f i) <= #(⋃ i, f i) :=
  ciSup_le' fun _ => mk_le_mk_of_subset (subset_iUnion _ _)

/--
theorem `mk_iUnion_le_sum_mk` / 定理 `mk_iUnion_le_sum_mk`

English:
theorem mk_iUnion_le_sum_mk
  given: {α ι : Type u} {f : ι -> Set α}
  statement: #(⋃ i, f i) <= sum fun i => #(f i)
  proof: calc
    #(⋃ i, f i) <= #(Σ i, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

中文:
定理 mk_iUnion_le_sum_mk
  条件: {α ι : 类型u} {f : ι -> Set α}
  结论: #(⋃ i, f i) <= sum fun i => #(f i)
  证明: calc
    #(⋃ i, f i) <= #(Σ i, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

Depends on / 依赖: Set.sigmaToiUnion_surjective, mk_le_of_surjective, mk_sigma, sigmaToiUnion_surjective
-/
theorem mk_iUnion_le_sum_mk {α ι : Type u} {f : ι -> Set α} : #(⋃ i, f i) <= sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) <= #(Σ i, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

/--
theorem `mk_iUnion_le_sum_mk_lift` / 定理 `mk_iUnion_le_sum_mk_lift`

English:
theorem mk_iUnion_le_sum_mk_lift
  given: {α : Type u} {ι : Type v} {f : ι -> Set α}
  proof: calc
    lift.{v} #(⋃ i, f i) <= #(Σ i, f i) :=
mk_le_of_surjective ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

中文:
定理 mk_iUnion_le_sum_mk_lift
  条件: {α : 类型u} {ι : 类型v} {f : ι -> Set α}
  证明: calc
    lift.{v} #(⋃ i, f i) <= #(Σ i, f i) :=
mk_le_of_surjective ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

Depends on / 依赖: Set.sigmaToiUnion_surjective, ULift.up_surjective.comp, mk_le_of_surjective, mk_sigma, sigmaToiUnion_surjective, up_surjective
-/
theorem mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι -> Set α} :
    lift.{v} #(⋃ i, f i) <= sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) <= #(Σ i, f i) :=
mk_le_of_surjective ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

/--
theorem `mk_iUnion_eq_sum_mk` / 定理 `mk_iUnion_eq_sum_mk`

English:
theorem mk_iUnion_eq_sum_mk
  statement: {α ι : Type u} {f : ι -> Set α}
  proof: calc
    #(⋃ i, f i) = #(Σ i, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

中文:
定理 mk_iUnion_eq_sum_mk
  结论: {α ι : 类型u} {f : ι -> Set α}
  证明: calc
    #(⋃ i, f i) = #(Σ i, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

Depends on / 依赖: Set.unionEqSigmaOfDisjoint, mk_congr, mk_sigma, unionEqSigmaOfDisjoint
-/
theorem mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι -> Set α}
    (h : Pairwise (Disjoint on f)) : #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) = #(Σ i, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

/--
theorem `mk_iUnion_eq_sum_mk_lift` / 定理 `mk_iUnion_eq_sum_mk_lift`

English:
theorem mk_iUnion_eq_sum_mk_lift
  statement: {α : Type u} {ι : Type v} {f : ι -> Set α}
  proof: calc
    lift.{v} #(⋃ i, f i) = #(Σ i, f i) :=
mk_congr .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

中文:
定理 mk_iUnion_eq_sum_mk_lift
  结论: {α : 类型u} {ι : 类型v} {f : ι -> Set α}
  证明: calc
    lift.{v} #(⋃ i, f i) = #(Σ i, f i) :=
mk_congr .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

Depends on / 依赖: Equiv.ulift, Nat.isUniformEmbedding_coe_real.comapMetricSpace, Set.unionEqSigmaOfDisjoint, comapMetricSpace, isUniformEmbedding_coe_real, mk_congr, mk_sigma, unionEqSigmaOfDisjoint
-/
theorem mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι -> Set α}
    (h : Pairwise (Disjoint on f)) :
    lift.{v} #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) = #(Σ i, f i) :=
mk_congr .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

/--
theorem `mk_iUnion_le` / 定理 `mk_iUnion_le`

English:
theorem mk_iUnion_le
  given: {α ι : Type u} (f : ι -> Set α)
  statement: #(⋃ i, f i) <= #ι * ⨆ i, #(f i)
  proof: mk_iUnion_le_sum_mk.trans (sum_le_mk_mul_iSup _)

中文:
定理 mk_iUnion_le
  条件: {α ι : 类型u} (f : ι -> Set α)
  结论: #(⋃ i, f i) <= #ι * ⨆ i, #(f i)
  证明: mk_iUnion_le_sum_mk.trans (sum_le_mk_mul_iSup _)

Depends on / 依赖: mk_iUnion_le_sum_mk, mk_iUnion_le_sum_mk.trans, sum_le_mk_mul_iSup
-/
theorem mk_iUnion_le {α ι : Type u} (f : ι -> Set α) : #(⋃ i, f i) <= #ι * ⨆ i, #(f i) :=
  mk_iUnion_le_sum_mk.trans (sum_le_mk_mul_iSup _)

/--
theorem `mk_iUnion_le_lift` / 定理 `mk_iUnion_le_lift`

English:
theorem mk_iUnion_le_lift
  given: {α : Type u} {ι : Type v} (f : ι -> Set α)
  proof: by
refine mk_iUnion_le_sum_mk_lift.trans Eq.trans_le ?_ (sum_le_lift_mk_mul_iSup _)
  rw [← lift_sum]; rw [lift_id'.{_]; rw [u}]

中文:
定理 mk_iUnion_le_lift
  条件: {α : 类型u} {ι : 类型v} (f : ι -> Set α)
  证明: by
refine mk_iUnion_le_sum_mk_lift.trans Eq.trans_le ?_ (sum_le_lift_mk_mul_iSup _)
  rw [← lift_sum]; rw [lift_id'.{_]; rw [u}]

Depends on / 依赖: Eq.trans_le, lift_id, lift_sum, mk_iUnion_le_sum_mk_lift, mk_iUnion_le_sum_mk_lift.trans, sum_le_lift_mk_mul_iSup, trans_le
-/
theorem mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι -> Set α) :
    lift.{v} #(⋃ i, f i) <= lift.{u} #ι * ⨆ i, lift.{v} #(f i) := by
refine mk_iUnion_le_sum_mk_lift.trans Eq.trans_le ?_ (sum_le_lift_mk_mul_iSup _)
  rw [← lift_sum]; rw [lift_id'.{_]; rw [u}]

/--
theorem `mk_sUnion_le` / 定理 `mk_sUnion_le`

English:
theorem mk_sUnion_le
  given: {α : Type u} (A : Set (Set α))
  statement: #(⋃₀ A) <= #A * ⨆ s : A, #s
  proof: by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le

中文:
定理 mk_sUnion_le
  条件: {α : 类型u} (A : Set (Set α))
  结论: #(⋃₀ A) <= #A * ⨆ s : A, #s
  证明: by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le

Depends on / 依赖: mk_iUnion_le, sUnion_eq_iUnion
-/
theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) <= #A * ⨆ s : A, #s := by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le

/--
theorem `mk_biUnion_le` / 定理 `mk_biUnion_le`

English:
theorem mk_biUnion_le
  given: {ι α : Type u} (A : ι -> Set α) (s : Set ι)
  proof: by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

中文:
定理 mk_biUnion_le
  条件: {ι α : 类型u} (A : ι -> Set α) (s : Set ι)
  证明: by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

Depends on / 依赖: biUnion_eq_iUnion, mk_iUnion_le
-/
theorem mk_biUnion_le {ι α : Type u} (A : ι -> Set α) (s : Set ι) :
    #(⋃ x in s, A x) <= #s * ⨆ x : s, #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

/--
theorem `mk_biUnion_le_lift` / 定理 `mk_biUnion_le_lift`

English:
theorem mk_biUnion_le_lift
  given: {α : Type u} {ι : Type v} (A : ι -> Set α) (s : Set ι)
  proof: by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

中文:
定理 mk_biUnion_le_lift
  条件: {α : 类型u} {ι : 类型v} (A : ι -> Set α) (s : Set ι)
  证明: by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

Depends on / 依赖: biUnion_eq_iUnion, mk_iUnion_le_lift
-/
theorem mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι -> Set α) (s : Set ι) :
    lift.{v} #(⋃ x in s, A x) <= lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

/--
theorem `finset_card_lt_aleph0` / 定理 `finset_card_lt_aleph0`

English:
theorem finset_card_lt_aleph0
  given: (s : Finset α)
  statement: #(↑s : Set α) < ℵ₀
  proof: lt_aleph0_of_finite _

中文:
定理 finset_card_lt_aleph0
  条件: (s : Finset α)
  结论: #(↑s : Set α) < ℵ₀
  证明: lt_aleph0_of_finite _

Depends on / 依赖: lt_aleph0_of_finite
-/
theorem finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀ :=
  lt_aleph0_of_finite _

/--
theorem `mk_set_eq_nat_iff_finset` / 定理 `mk_set_eq_nat_iff_finset`

English:
theorem mk_set_eq_nat_iff_finset
  given: {α} {s : Set α} {n : Nat}
  proof: by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ natCast_lt_aleph0)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset

中文:
定理 mk_set_eq_nat_iff_finset
  条件: {α} {s : Set α} {n : 自然数}
  证明: by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ natCast_lt_aleph0)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset

Depends on / 依赖: Finset, h.symm, lt_aleph0_iff_set_finite, mk_coe_finset, natCast_lt_aleph0
-/
theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : Nat} :
    #s = n ↔ exists t : Finset α, (t : Set α) = s ∧ t.card = n := by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ natCast_lt_aleph0)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset

/--
theorem `mk_eq_nat_iff_finset` / 定理 `mk_eq_nat_iff_finset`

English:
theorem mk_eq_nat_iff_finset
  given: {n : Nat}
  proof: by
  rw [← mk_univ]; rw [mk_set_eq_nat_iff_finset]

中文:
定理 mk_eq_nat_iff_finset
  条件: {n : 自然数}
  证明: by
  rw [← mk_univ]; rw [mk_set_eq_nat_iff_finset]

Depends on / 依赖: mk_set_eq_nat_iff_finset, mk_univ
-/
theorem mk_eq_nat_iff_finset {n : Nat} :
    #α = n ↔ exists t : Finset α, (t : Set α) = univ ∧ t.card = n := by
  rw [← mk_univ]; rw [mk_set_eq_nat_iff_finset]

/--
theorem `mk_eq_nat_iff_fintype` / 定理 `mk_eq_nat_iff_fintype`

English:
theorem mk_eq_nat_iff_fintype
  given: {n : Nat}
  statement: #α = n ↔ exists h : Fintype α, @Fintype.card α h = n
  proof: by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩

中文:
定理 mk_eq_nat_iff_fintype
  条件: {n : 自然数}
  结论: #α = n ↔ 存在 h : Fintype α, @Fintype.card α h = n
  证明: by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩

Depends on / 依赖: eq_univ_iff_forall, mk_eq_nat_iff_finset
-/
theorem mk_eq_nat_iff_fintype {n : Nat} : #α = n ↔ exists h : Fintype α, @Fintype.card α h = n := by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩

/--
theorem `mk_set_eq_one_iff` / 定理 `mk_set_eq_one_iff`

English:
theorem mk_set_eq_one_iff
  given: {s : Set α}
  statement: #s = 1 ↔ exists x, s = {x}
  proof: by
  rw [eq_one_iff_unique]; rw [Set.exists_eq_singleton_iff_nonempty_subsingleton]; rw [Set.nonempty_coe_sort]; rw [Set.subsingleton_coe]; rw [and_comm]

中文:
定理 mk_set_eq_one_iff
  条件: {s : Set α}
  结论: #s = 1 ↔ 存在 x, s = {x}
  证明: by
  rw [eq_one_iff_unique]; rw [Set.exists_eq_singleton_iff_nonempty_subsingleton]; rw [Set.nonempty_coe_sort]; rw [Set.subsingleton_coe]; rw [and_comm]

Depends on / 依赖: Set.exists_eq_singleton_iff_nonempty_subsingleton, Set.nonempty_coe_sort, Set.subsingleton_coe, and_comm, eq_one_iff_unique, exists_eq_singleton_iff_nonempty_subsingleton, nonempty_coe_sort, subsingleton_coe
-/
theorem mk_set_eq_one_iff {s : Set α} : #s = 1 ↔ exists x, s = {x} := by
  rw [eq_one_iff_unique]; rw [Set.exists_eq_singleton_iff_nonempty_subsingleton]; rw [Set.nonempty_coe_sort]; rw [Set.subsingleton_coe]; rw [and_comm]

/--
theorem `mk_union_add_mk_inter` / 定理 `mk_union_add_mk_inter`

English:
theorem mk_union_add_mk_inter
  given: {α : Type u} {S T : Set α}
  proof: by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

中文:
定理 mk_union_add_mk_inter
  条件: {α : 类型u} {S T : Set α}
  证明: by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

Depends on / 依赖: Equiv.Set.unionSumInter, Quot.sound, classical, unionSumInter
-/
theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    #(S union T : Set α) + #(S inter T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

/--
theorem `mk_union_le` / 定理 `mk_union_le`

English:
theorem mk_union_le
  given: {α : Type u} (S T : Set α)
  statement: #(S union T : Set α) <= #S + #T
  proof: @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S union T : Set α) #(S inter T : Set α)

中文:
定理 mk_union_le
  条件: {α : 类型u} (S T : Set α)
  结论: #(S union T : Set α) <= #S + #T
  证明: @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S union T : Set α) #(S inter T : Set α)

Depends on / 依赖: mk_union_add_mk_inter, self_le_add_right
-/
theorem mk_union_le {α : Type u} (S T : Set α) : #(S union T : Set α) <= #S + #T :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S union T : Set α) #(S inter T : Set α)

/--
theorem `mk_union_of_disjoint` / 定理 `mk_union_of_disjoint`

English:
theorem mk_union_of_disjoint
  given: {α : Type u} {S T : Set α} (H : Disjoint S T)
  proof: by
  classical
  exact Quot.sound ⟨Equiv.Set.union H⟩

中文:
定理 mk_union_of_disjoint
  条件: {α : 类型u} {S T : Set α} (H : Disjoint S T)
  证明: by
  classical
  exact Quot.sound ⟨Equiv.Set.union H⟩

Depends on / 依赖: Equiv.Set.union, Quot.sound, classical
-/
theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    #(S union T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.union H⟩

/--
theorem `mk_insert` / 定理 `mk_insert`

English:
theorem mk_insert
  given: {α : Type u} {s : Set α} {a : α} (h : a ∉ s)
  proof: by
  rw [← union_singleton]; rw [mk_union_of_disjoint]; rw [mk_singleton]
  simpa

中文:
定理 mk_insert
  条件: {α : 类型u} {s : Set α} {a : α} (h : a ∉ s)
  证明: by
  rw [← union_singleton]; rw [mk_union_of_disjoint]; rw [mk_singleton]
  simpa

Depends on / 依赖: mk_singleton, mk_union_of_disjoint, union_singleton
-/
theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by
  rw [← union_singleton]; rw [mk_union_of_disjoint]; rw [mk_singleton]
  simpa

/--
theorem `mk_insert_le` / 定理 `mk_insert_le`

English:
theorem mk_insert_le
  given: {α : Type u} {s : Set α} {a : α}
  statement: #(insert a s : Set α) <= #s + 1
  proof: by
  by_cases h : a in s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]

中文:
定理 mk_insert_le
  条件: {α : 类型u} {s : Set α} {a : α}
  结论: #(insert a s : Set α) <= #s + 1
  证明: by
  by_cases h : a in s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]

Depends on / 依赖: insert_eq_of_mem, mk_insert, self_le_add_right
-/
theorem mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) <= #s + 1 := by
  by_cases h : a in s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]

/--
theorem `mk_sum_compl` / 定理 `mk_sum_compl`

English:
theorem mk_sum_compl
  given: {α} (s : Set α)
  statement: #s + #(sᶜ : Set α) = #α
  proof: by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

中文:
定理 mk_sum_compl
  条件: {α} (s : Set α)
  结论: #s + #(sᶜ : Set α) = #α
  证明: by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

Depends on / 依赖: Equiv.Set.sumCompl, classical, mk_congr, sumCompl
-/
theorem mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α := by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

/--
theorem `mk_le_iff_forall_finset_subset_card_le` / 定理 `mk_le_iff_forall_finset_subset_card_le`

English:
theorem mk_le_iff_forall_finset_subset_card_le
  given: {α : Type u} {n : Nat} {t : Set α}
  proof: by
  refine ⟨fun H s hs => by simpa using (mk_le_mk_of_subset hs).trans H, fun H => ?_⟩
  apply card_le_of (fun s => ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  grind

中文:
定理 mk_le_iff_forall_finset_subset_card_le
  条件: {α : 类型u} {n : 自然数} {t : Set α}
  证明: by
  refine ⟨fun H s hs => by simpa using (mk_le_mk_of_subset hs).trans H, fun H => ?_⟩
  apply card_le_of (fun s => ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  grind

Depends on / 依赖: Finset, Finset.card_image_of_injOn, Subtype, Subtype.coe_injective.injOn, Subtype.val, card_image_of_injOn, card_le_of, classical, coe_injective, mk_le_mk_of_subset, s.card, s.image, u.card
-/
theorem mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : Nat} {t : Set α} :
    #t <= n ↔ forall s : Finset α, (s : Set α) subseteq t -> s.card <= n := by
  refine ⟨fun H s hs => by simpa using (mk_le_mk_of_subset hs).trans H, fun H => ?_⟩
  apply card_le_of (fun s => ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  grind

/--
theorem `mk_subtype_mono` / 定理 `mk_subtype_mono`

English:
theorem mk_subtype_mono
  given: {p q : α -> Prop} (h : forall x, p x -> q x)
  proof: ⟨embeddingOfSubset _ _ h⟩

中文:
定理 mk_subtype_mono
  条件: {p q : α -> 命题} (h : 对任意 x, p x -> q x)
  证明: ⟨embeddingOfSubset _ _ h⟩

Depends on / 依赖: embeddingOfSubset
-/
theorem mk_subtype_mono {p q : α -> Prop} (h : forall x, p x -> q x) :
    #{ x // p x } <= #{ x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩

/--
lemma `card_lt_card_of_right_finite` / 引理 `card_lt_card_of_right_finite`

English:
lemma card_lt_card_of_right_finite
  given: {A B : Set α} (hfin : B.Finite) (hlt : A ⊂ B)
  statement: #A < #B
  proof: by
  have : Fintype A := (hfin.subset hlt.subset).fintype
  have : Fintype B := hfin.fintype
simpa using Finset.card_lt_card Set.toFinset_ssubset_toFinset.mpr hlt

中文:
引理 card_lt_card_of_right_finite
  条件: {A B : Set α} (hfin : B.Finite) (hlt : A ⊂ B)
  结论: #A < #B
  证明: by
  have : Fintype A := (hfin.subset hlt.subset).fintype
  have : Fintype B := hfin.fintype
simpa using Finset.card_lt_card Set.toFinset_ssubset_toFinset.mpr hlt

Depends on / 依赖: Finset, Finset.card_lt_card, Fintype, Set.toFinset_ssubset_toFinset.mpr, card_lt_card, fintype, hfin.fintype, hfin.subset, hlt.subset, subset, toFinset_ssubset_toFinset
-/
lemma card_lt_card_of_right_finite {A B : Set α} (hfin : B.Finite) (hlt : A ⊂ B) : #A < #B := by
  have : Fintype A := (hfin.subset hlt.subset).fintype
  have : Fintype B := hfin.fintype
simpa using Finset.card_lt_card Set.toFinset_ssubset_toFinset.mpr hlt

/--
lemma `card_lt_card_of_left_finite` / 引理 `card_lt_card_of_left_finite`

English:
lemma card_lt_card_of_left_finite
  given: {A B : Set α} (hfin : A.Finite) (hlt : A ⊂ B)
  statement: #A < #B
  proof: by
  rcases finite_or_infinite B with hfin | hinf
  · exact card_lt_card_of_right_finite hfin hlt
· exact (lt_aleph0_iff_subtype_finite.mpr hfin).trans_le Cardinal.aleph0_le_mk_iff.mpr hinf

中文:
引理 card_lt_card_of_left_finite
  条件: {A B : Set α} (hfin : A.Finite) (hlt : A ⊂ B)
  结论: #A < #B
  证明: by
  rcases finite_or_infinite B with hfin | hinf
  · exact card_lt_card_of_right_finite hfin hlt
· exact (lt_aleph0_iff_subtype_finite.mpr hfin).trans_le Cardinal.aleph0_le_mk_iff.mpr hinf

Depends on / 依赖: Cardinal, Cardinal.aleph0_le_mk_iff.mpr, aleph0_le_mk_iff, card_lt_card_of_right_finite, finite_or_infinite, lt_aleph0_iff_subtype_finite, lt_aleph0_iff_subtype_finite.mpr, trans_le
-/
lemma card_lt_card_of_left_finite {A B : Set α} (hfin : A.Finite) (hlt : A ⊂ B) : #A < #B := by
  rcases finite_or_infinite B with hfin | hinf
  · exact card_lt_card_of_right_finite hfin hlt
· exact (lt_aleph0_iff_subtype_finite.mpr hfin).trans_le Cardinal.aleph0_le_mk_iff.mpr hinf

/--
theorem `mk_strictMono` / 定理 `mk_strictMono`

English:
theorem mk_strictMono
  given: [Finite α]
  statement: StrictMono (α := Set α) (mk ∘ (↑))
  proof: fun _ s => card_lt_card_of_right_finite s.toFinite

中文:
定理 mk_strictMono
  条件: [Finite α]
  结论: StrictMono (α := Set α) (mk ∘ (↑))
  证明: fun _ s => card_lt_card_of_right_finite s.toFinite
-/
theorem mk_strictMono [Finite α] : StrictMono (α := Set α) (mk ∘ (↑)) :=
  fun _ s => card_lt_card_of_right_finite s.toFinite

/--
theorem `mk_strictMonoOn` / 定理 `mk_strictMonoOn`

English:
theorem mk_strictMonoOn
  statement: StrictMonoOn (mk ∘ (↑)) {s : Set α | s.Finite}
  proof: fun _ _ _ => card_lt_card_of_right_finite

中文:
定理 mk_strictMonoOn
  结论: StrictMonoOn (mk ∘ (↑)) {s : Set α | s.Finite}
  证明: fun _ _ _ => card_lt_card_of_right_finite

Depends on / 依赖: card_lt_card_of_right_finite
-/
theorem mk_strictMonoOn : StrictMonoOn (mk ∘ (↑)) {s : Set α | s.Finite} :=
  fun _ _ _ => card_lt_card_of_right_finite

/--
theorem `le_mk_sdiff_add_mk` / 定理 `le_mk_sdiff_add_mk`

English:
theorem le_mk_sdiff_add_mk
  given: (S T : Set α)
  statement: #S <= #(S \ T : Set α) + #T
  proof: (mk_le_mk_of_subset <| subset_sdiff_union _ _).trans mk_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_mk_diff_add_mk := le_mk_sdiff_add_mk

中文:
定理 le_mk_sdiff_add_mk
  条件: (S T : Set α)
  结论: #S <= #(S \ T : Set α) + #T
  证明: (mk_le_mk_of_subset <| subset_sdiff_union _ _).trans mk_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_mk_diff_add_mk := le_mk_sdiff_add_mk

Depends on / 依赖: mk_le_mk_of_subset, mk_union_le, subset_sdiff_union
-/
theorem le_mk_sdiff_add_mk (S T : Set α) : #S <= #(S \ T : Set α) + #T :=
(mk_le_mk_of_subset <| subset_sdiff_union _ _).trans mk_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_mk_diff_add_mk := le_mk_sdiff_add_mk

/--
theorem `mk_sdiff_add_mk` / 定理 `mk_sdiff_add_mk`

English:
theorem mk_sdiff_add_mk
  given: {S T : Set α} (h : T subseteq S)
  statement: #(S \ T : Set α) + #T = #S
  proof: by
refine (mk_union_of_disjoint <| ?_).symm.trans by rw [sdiff_union_of_subset h]
  exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mk_diff_add_mk := mk_sdiff_add_mk

中文:
定理 mk_sdiff_add_mk
  条件: {S T : Set α} (h : T subseteq S)
  结论: #(S \ T : Set α) + #T = #S
  证明: by
refine (mk_union_of_disjoint <| ?_).symm.trans by rw [sdiff_union_of_subset h]
  exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mk_diff_add_mk := mk_sdiff_add_mk

Depends on / 依赖: disjoint_sdiff_self_left, mk_union_of_disjoint, sdiff_union_of_subset, symm.trans
-/
theorem mk_sdiff_add_mk {S T : Set α} (h : T subseteq S) : #(S \ T : Set α) + #T = #S := by
refine (mk_union_of_disjoint <| ?_).symm.trans by rw [sdiff_union_of_subset h]
  exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mk_diff_add_mk := mk_sdiff_add_mk

/--
lemma `sdiff_nonempty_of_mk_lt_mk` / 引理 `sdiff_nonempty_of_mk_lt_mk`

English:
lemma sdiff_nonempty_of_mk_lt_mk
  given: {S T : Set α} (h : #S < #T)
  statement: (T \ S).Nonempty
  proof: by
  rw [← mk_set_ne_zero_iff]
  intro h'
  exact h.not_ge ((le_mk_sdiff_add_mk T S).trans (by simp [h']))

@[deprecated (since := "2026-06-03")] alias diff_nonempty_of_mk_lt_mk := sdiff_nonempty_of_mk_lt_mk

中文:
引理 sdiff_nonempty_of_mk_lt_mk
  条件: {S T : Set α} (h : #S < #T)
  结论: (T \ S).Nonempty
  证明: by
  rw [← mk_set_ne_zero_iff]
  intro h'
  exact h.not_ge ((le_mk_sdiff_add_mk T S).trans (by simp [h']))

@[deprecated (since := "2026-06-03")] alias diff_nonempty_of_mk_lt_mk := sdiff_nonempty_of_mk_lt_mk

Depends on / 依赖: h.not_ge, le_mk_sdiff_add_mk, mk_set_ne_zero_iff, not_ge
-/
lemma sdiff_nonempty_of_mk_lt_mk {S T : Set α} (h : #S < #T) : (T \ S).Nonempty := by
  rw [← mk_set_ne_zero_iff]
  intro h'
  exact h.not_ge ((le_mk_sdiff_add_mk T S).trans (by simp [h']))

@[deprecated (since := "2026-06-03")] alias diff_nonempty_of_mk_lt_mk := sdiff_nonempty_of_mk_lt_mk

/--
lemma `compl_nonempty_of_mk_lt_mk` / 引理 `compl_nonempty_of_mk_lt_mk`

English:
lemma compl_nonempty_of_mk_lt_mk
  given: {S : Set α} (h : #S < #α)
  statement: Sᶜ.Nonempty
  proof: by
  rw [← mk_univ (α := α)] at h
  simpa [Set.compl_eq_univ_sdiff] using sdiff_nonempty_of_mk_lt_mk h

中文:
引理 compl_nonempty_of_mk_lt_mk
  条件: {S : Set α} (h : #S < #α)
  结论: Sᶜ.Nonempty
  证明: by
  rw [← mk_univ (α := α)] at h
  simpa [Set.compl_eq_univ_sdiff] using sdiff_nonempty_of_mk_lt_mk h

Depends on / 依赖: Set.compl_eq_univ_sdiff, compl_eq_univ_sdiff, mk_univ, sdiff_nonempty_of_mk_lt_mk
-/
lemma compl_nonempty_of_mk_lt_mk {S : Set α} (h : #S < #α) : Sᶜ.Nonempty := by
  rw [← mk_univ (α := α)] at h
  simpa [Set.compl_eq_univ_sdiff] using sdiff_nonempty_of_mk_lt_mk h

/--
theorem `mk_union_le_aleph0` / 定理 `mk_union_le_aleph0`

English:
theorem mk_union_le_aleph0
  given: {α} {P Q : Set α}
  proof: by
  simp only [le_aleph0_iff_subtype_countable, ofPred_mem_eq, Set.union_def,
    ← countable_union]

中文:
定理 mk_union_le_aleph0
  条件: {α} {P Q : Set α}
  证明: by
  simp only [le_aleph0_iff_subtype_countable, ofPred_mem_eq, Set.union_def,
    ← countable_union]

Depends on / 依赖: Set.union_def, countable_union, le_aleph0_iff_subtype_countable, ofPred_mem_eq, union_def
-/
theorem mk_union_le_aleph0 {α} {P Q : Set α} :
    #(P union Q : Set α) <= ℵ₀ ↔ #P <= ℵ₀ ∧ #Q <= ℵ₀ := by
  simp only [le_aleph0_iff_subtype_countable, ofPred_mem_eq, Set.union_def,
    ← countable_union]

/--
theorem `mk_sep` / 定理 `mk_sep`

English:
theorem mk_sep
  given: (s : Set α) (t : α -> Prop)
  statement: #({ x in s | t x } : Set α) = #{ x : s | t x.1 }
  proof: mk_congr (Equiv.Set.sep s t)

中文:
定理 mk_sep
  条件: (s : Set α) (t : α -> 命题)
  结论: #({ x in s | t x } : Set α) = #{ x : s | t x.1 }
  证明: mk_congr (Equiv.Set.sep s t)

Depends on / 依赖: Equiv.Set.sep, mk_congr
-/
theorem mk_sep (s : Set α) (t : α -> Prop) : #({ x in s | t x } : Set α) = #{ x : s | t x.1 } :=
  mk_congr (Equiv.Set.sep s t)

/--
theorem `mk_preimage_of_injective_lift` / 定理 `mk_preimage_of_injective_lift`

English:
theorem mk_preimage_of_injective_lift
  statement: {α : Type u} {β : Type v} (f : α -> β) (s : Set β)
  proof: by
  rw [lift_mk_le.{0}]
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective

中文:
定理 mk_preimage_of_injective_lift
  结论: {α : 类型u} {β : 类型v} (f : α -> β) (s : Set β)
  证明: by
  rw [lift_mk_le.{0}]
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.coind, Subtype.coind_injective, Subtype.val_injective, coind_injective, h.comp, lift_mk_le, mem_preimage, mem_preimage.mp, val_injective
-/
theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set β)
    (h : Injective f) : lift.{v} #(f ⁻¹' s) <= lift.{u} #s := by
  rw [lift_mk_le.{0}]
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective

/--
theorem `mk_preimage_of_subset_range_lift` / 定理 `mk_preimage_of_subset_range_lift`

English:
theorem mk_preimage_of_subset_range_lift
  statement: {α : Type u} {β : Type v} (f : α -> β) (s : Set β)
  proof: by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

中文:
定理 mk_preimage_of_subset_range_lift
  结论: {α : 类型u} {β : 类型v} (f : α -> β) (s : Set β)
  证明: by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

Depends on / 依赖: image_preimage_eq_iff, mk_image_le_lift, nth_rewrite
-/
theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set β)
    (h : s subseteq range f) : lift.{u} #s <= lift.{v} #(f ⁻¹' s) := by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

/--
theorem `mk_preimage_of_injective_of_subset_range_lift` / 定理 `mk_preimage_of_injective_of_subset_range_lift`

English:
theorem mk_preimage_of_injective_of_subset_range_lift
  statement: {β : Type v} (f : α -> β) (s : Set β)
  proof: le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

中文:
定理 mk_preimage_of_injective_of_subset_range_lift
  结论: {β : 类型v} (f : α -> β) (s : Set β)
  证明: le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

Depends on / 依赖: le_antisymm, mk_preimage_of_injective_lift, mk_preimage_of_subset_range_lift
-/
theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α -> β) (s : Set β)
    (h : Injective f) (h2 : s subseteq range f) : lift.{v} #(f ⁻¹' s) = lift.{u} #s :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

/--
theorem `mk_preimage_of_injective_of_subset_range` / 定理 `mk_preimage_of_injective_of_subset_range`

English:
theorem mk_preimage_of_injective_of_subset_range
  statement: (f : α -> β) (s : Set β) (h : Injective f)
  proof: by
  convert! mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

@[simp]

中文:
定理 mk_preimage_of_injective_of_subset_range
  结论: (f : α -> β) (s : Set β) (h : Injective f)
  证明: by
  convert! mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

@[simp]

Depends on / 依赖: convert, lift_id, mk_preimage_of_injective_of_subset_range_lift
-/
theorem mk_preimage_of_injective_of_subset_range (f : α -> β) (s : Set β) (h : Injective f)
    (h2 : s subseteq range f) : #(f ⁻¹' s) = #s := by
  convert! mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

@[simp]
/--
theorem `mk_preimage_equiv_lift` / 定理 `mk_preimage_equiv_lift`

English:
theorem mk_preimage_equiv_lift
  given: {β : Type v} (f : α ≃ β) (s : Set β)
  proof: by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ => ⟨⟩

@[simp]

中文:
定理 mk_preimage_equiv_lift
  条件: {β : 类型v} (f : α ≃ β) (s : Set β)
  证明: by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ => ⟨⟩

@[simp]

Depends on / 依赖: f.injective, f.range_eq_univ, injective, mk_preimage_of_injective_of_subset_range_lift, range_eq_univ
-/
theorem mk_preimage_equiv_lift {β : Type v} (f : α ≃ β) (s : Set β) :
    lift.{v} #(f ⁻¹' s) = lift.{u} #s := by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ => ⟨⟩

@[simp]
/--
theorem `mk_preimage_equiv` / 定理 `mk_preimage_equiv`

English:
theorem mk_preimage_equiv
  given: (f : α ≃ β) (s : Set β)
  statement: #(f ⁻¹' s) = #s
  proof: by
  simpa using mk_preimage_equiv_lift f s

中文:
定理 mk_preimage_equiv
  条件: (f : α ≃ β) (s : Set β)
  结论: #(f ⁻¹' s) = #s
  证明: by
  simpa using mk_preimage_equiv_lift f s

Depends on / 依赖: mk_preimage_equiv_lift
-/
theorem mk_preimage_equiv (f : α ≃ β) (s : Set β) : #(f ⁻¹' s) = #s := by
  simpa using mk_preimage_equiv_lift f s

/--
theorem `mk_preimage_of_injective` / 定理 `mk_preimage_of_injective`

English:
theorem mk_preimage_of_injective
  given: (f : α -> β) (s : Set β) (h : Injective f)
  proof: by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

中文:
定理 mk_preimage_of_injective
  条件: (f : α -> β) (s : Set β) (h : Injective f)
  证明: by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

Depends on / 依赖: lift_id, mk_preimage_of_injective_lift
-/
theorem mk_preimage_of_injective (f : α -> β) (s : Set β) (h : Injective f) :
    #(f ⁻¹' s) <= #s := by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

/--
theorem `mk_preimage_of_subset_range` / 定理 `mk_preimage_of_subset_range`

English:
theorem mk_preimage_of_subset_range
  given: (f : α -> β) (s : Set β) (h : s subseteq range f)
  proof: by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h

中文:
定理 mk_preimage_of_subset_range
  条件: (f : α -> β) (s : Set β) (h : s subseteq range f)
  证明: by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h

Depends on / 依赖: lift_id, mk_preimage_of_subset_range_lift
-/
theorem mk_preimage_of_subset_range (f : α -> β) (s : Set β) (h : s subseteq range f) :
    #s <= #(f ⁻¹' s) := by
  rw [← lift_id #(↑(f ⁻¹' s))]; rw [← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h

/--
theorem `mk_subset_ge_of_subset_image_lift` / 定理 `mk_subset_ge_of_subset_image_lift`

English:
theorem mk_subset_ge_of_subset_image_lift
  statement: {α : Type u} {β : Type v} (f : α -> β) {s : Set α}
  proof: by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

中文:
定理 mk_subset_ge_of_subset_image_lift
  结论: {α : 类型u} {β : 类型v} (f : α -> β) {s : Set α}
  证明: by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

Depends on / 依赖: convert, image_eq_range, mk_preimage_of_subset_range_lift, mk_sep
-/
theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α -> β) {s : Set α}
    {t : Set β} (h : t subseteq f '' s) : lift.{u} #t <= lift.{v} #({ x in s | f x in t } : Set α) := by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

/--
theorem `mk_subset_ge_of_subset_image` / 定理 `mk_subset_ge_of_subset_image`

English:
theorem mk_subset_ge_of_subset_image
  given: (f : α -> β) {s : Set α} {t : Set β} (h : t subseteq f '' s)
  proof: by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

中文:
定理 mk_subset_ge_of_subset_image
  条件: (f : α -> β) {s : Set α} {t : Set β} (h : t subseteq f '' s)
  证明: by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

Depends on / 依赖: convert, image_eq_range, mk_preimage_of_subset_range, mk_sep
-/
theorem mk_subset_ge_of_subset_image (f : α -> β) {s : Set α} {t : Set β} (h : t subseteq f '' s) :
    #t <= #({ x in s | f x in t } : Set α) := by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

/--
theorem `le_mk_iff_exists_subset` / 定理 `le_mk_iff_exists_subset`

English:
theorem le_mk_iff_exists_subset
  given: {c : Cardinal} {α : Type u} {s : Set α}
  proof: by
  rw [le_mk_iff_exists_set]; rw [← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]

中文:
定理 le_mk_iff_exists_subset
  条件: {c : Cardinal} {α : 类型u} {s : Set α}
  证明: by
  rw [le_mk_iff_exists_set]; rw [← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.exists_set_subtype, Subtype.val_injective, exists_congr, exists_set_subtype, le_mk_iff_exists_set, mk_image_eq, val_injective
-/
theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c <= #s ↔ exists p : Set α, p subseteq s ∧ #p = c := by
  rw [le_mk_iff_exists_set]; rw [← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]
/--
theorem `mk_range_inl` / 定理 `mk_range_inl`

English:
theorem mk_range_inl
  given: {α : Type u} {β : Type v}
  statement: #(range (@Sum.inl α β)) = lift.{v} #α
  proof: by
  rw [← lift_id'.{u]; rw [v} #_]; rw [(Equiv.Set.rangeInl α β).lift_cardinal_eq]; rw [lift_umax.{u]; rw [v}]

@[simp]

中文:
定理 mk_range_inl
  条件: {α : 类型u} {β : 类型v}
  结论: #(range (@Sum.inl α β)) = lift.{v} #α
  证明: by
  rw [← lift_id'.{u]; rw [v} #_]; rw [(Equiv.Set.rangeInl α β).lift_cardinal_eq]; rw [lift_umax.{u]; rw [v}]

@[simp]

Depends on / 依赖: Equiv.Set.rangeInl, lift_cardinal_eq, lift_id, lift_umax, rangeInl
-/
theorem mk_range_inl {α : Type u} {β : Type v} : #(range (@Sum.inl α β)) = lift.{v} #α := by
  rw [← lift_id'.{u]; rw [v} #_]; rw [(Equiv.Set.rangeInl α β).lift_cardinal_eq]; rw [lift_umax.{u]; rw [v}]

@[simp]
/--
theorem `mk_range_inr` / 定理 `mk_range_inr`

English:
theorem mk_range_inr
  given: {α : Type u} {β : Type v}
  statement: #(range (@Sum.inr α β)) = lift.{u} #β
  proof: by
  rw [← lift_id'.{v]; rw [u} #_]; rw [(Equiv.Set.rangeInr α β).lift_cardinal_eq]; rw [lift_umax.{v]; rw [u}]

中文:
定理 mk_range_inr
  条件: {α : 类型u} {β : 类型v}
  结论: #(range (@Sum.inr α β)) = lift.{u} #β
  证明: by
  rw [← lift_id'.{v]; rw [u} #_]; rw [(Equiv.Set.rangeInr α β).lift_cardinal_eq]; rw [lift_umax.{v]; rw [u}]

Depends on / 依赖: Equiv.Set.rangeInr, lift_cardinal_eq, lift_id, lift_umax, rangeInr
-/
theorem mk_range_inr {α : Type u} {β : Type v} : #(range (@Sum.inr α β)) = lift.{u} #β := by
  rw [← lift_id'.{v]; rw [u} #_]; rw [(Equiv.Set.rangeInr α β).lift_cardinal_eq]; rw [lift_umax.{v]; rw [u}]

/--
theorem `two_le_iff` / 定理 `two_le_iff`

English:
theorem two_le_iff
  statement: (2 : Cardinal) <= #α ↔ exists x y : α, x != y
  proof: by
  rw [two_le_iff_one_lt]; rw [one_lt_iff_nontrivial]; rw [nontrivial_iff]

中文:
定理 two_le_iff
  结论: (2 : Cardinal) <= #α ↔ 存在 x y : α, x != y
  证明: by
  rw [two_le_iff_one_lt]; rw [one_lt_iff_nontrivial]; rw [nontrivial_iff]

Depends on / 依赖: nontrivial_iff, one_lt_iff_nontrivial, two_le_iff_one_lt
-/
theorem two_le_iff : (2 : Cardinal) <= #α ↔ exists x y : α, x != y := by
  rw [two_le_iff_one_lt]; rw [one_lt_iff_nontrivial]; rw [nontrivial_iff]

/--
theorem `two_le_iff'` / 定理 `two_le_iff'`

English:
theorem two_le_iff'
  given: (x : α)
  statement: (2 : Cardinal) <= #α ↔ exists y : α, y != x
  proof: by
  rw [two_le_iff]; rw [← nontrivial_iff]; rw [nontrivial_iff_exists_ne x]

中文:
定理 two_le_iff'
  条件: (x : α)
  结论: (2 : Cardinal) <= #α ↔ 存在 y : α, y != x
  证明: by
  rw [two_le_iff]; rw [← nontrivial_iff]; rw [nontrivial_iff_exists_ne x]

Depends on / 依赖: nontrivial_iff, nontrivial_iff_exists_ne, two_le_iff
-/
theorem two_le_iff' (x : α) : (2 : Cardinal) <= #α ↔ exists y : α, y != x := by
  rw [two_le_iff]; rw [← nontrivial_iff]; rw [nontrivial_iff_exists_ne x]

/--
theorem `mk_eq_two_iff` / 定理 `mk_eq_two_iff`

English:
theorem mk_eq_two_iff
  statement: #α = 2 ↔ exists x y : α, x != y ∧ ({x, y} : Set α) = univ
  proof: by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩

中文:
定理 mk_eq_two_iff
  结论: #α = 2 ↔ 存在 x y : α, x != y ∧ ({x, y} : Set α) = univ
  证明: by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩

Depends on / 依赖: Cardinal, Finset, Finset.card_eq_two, NNRat.cast_smul_eq_nnqsmul, Nat.cast_two, card_eq_two, cast_smul_eq_nnqsmul, cast_two, classical, fun_prop, mk_eq_nat_iff_finset
-/
theorem mk_eq_two_iff : #α = 2 ↔ exists x y : α, x != y ∧ ({x, y} : Set α) = univ := by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩

/--
theorem `mk_eq_two_iff'` / 定理 `mk_eq_two_iff'`

English:
theorem mk_eq_two_iff'
  given: (x : α)
  statement: #α = 2 ↔ exists! y, y != x
  proof: by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact 

中文:
定理 mk_eq_two_iff'
  条件: (x : α)
  结论: #α = 2 ↔ 存在! y, y != x
  证明: by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact 

Depends on / 依赖: eq_univ_iff_forall, eq_univ_of_forall, exacts, hne.symm, mem_insert_iff, mem_singleton_iff, mk_eq_two_iff, or_iff_not_imp_left, resolve_left, resolve_right
-/
theorem mk_eq_two_iff' (x : α) : #α = 2 ↔ exists! y, y != x := by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩

/--
theorem `exists_notMem_of_length_lt` / 定理 `exists_notMem_of_length_lt`

English:
theorem exists_notMem_of_length_lt
  given: {α : Type*} (l : List α) (h : ↑l.length < #α)
  proof: by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ <= #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ <= l.length := Nat.cast_le.mpr (List.toFinset_card_le l)

中文:
定理 exists_notMem_of_length_lt
  条件: {α : 类型} (l : List α) (h : ↑l.length < #α)
  证明: by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ <= #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ <= l.length := Nat.cast_le.mpr (List.toFinset_card_le l)

Depends on / 依赖: Cardinal, Cardinal.mk_coe_finset, List.mem_toFinset.mpr, List.toFinset_card_le, Nat.cast_le.mpr, Set.univ, cast_le, classical, contrapose, l.length, l.toFinset, l.toFinset.card, length, mem_toFinset, mk_coe_finset, mk_le_mk_of_subset, mk_univ, mk_univ.symm, toFinset, toFinset_card_le
-/
theorem exists_notMem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
    exists z : α, z ∉ l := by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ <= #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ <= l.length := Nat.cast_le.mpr (List.toFinset_card_le l)

/--
theorem `exists_ne_ne_of_three_le` / 定理 `exists_ne_ne_of_three_le`

English:
theorem exists_ne_ne_of_three_le
  given: {α : Type*} (h : 3 <= #α) (x y : α)
  statement: exists z : α, z != x ∧ z != y
  proof: by
  have : ↑(3 : Nat) <= #α := by simpa using h
  have : ↑(2 : Nat) < #α := by rwa [← natCast_add_one_le_iff, ← Nat.cast_add_one]
  have := exists_notMem_of_length_lt [x, y] this
  simpa [not_or] using this

@[deprecated (since := "2026-02-17")] alias three_le := exists_ne_ne_of_three_le

中文:
定理 exists_ne_ne_of_three_le
  条件: {α : 类型} (h : 3 <= #α) (x y : α)
  结论: 存在 z : α, z != x ∧ z != y
  证明: by
  have : ↑(3 : Nat) <= #α := by simpa using h
  have : ↑(2 : Nat) < #α := by rwa [← natCast_add_one_le_iff, ← Nat.cast_add_one]
  have := exists_notMem_of_length_lt [x, y] this
  simpa [not_or] using this

@[deprecated (since := "2026-02-17")] alias three_le := exists_ne_ne_of_three_le

Depends on / 依赖: Nat.cast_add_one, cast_add_one, exists_notMem_of_length_lt, natCast_add_one_le_iff, not_or
-/
theorem exists_ne_ne_of_three_le {α : Type*} (h : 3 <= #α) (x y : α) : exists z : α, z != x ∧ z != y := by
  have : ↑(3 : Nat) <= #α := by simpa using h
  have : ↑(2 : Nat) < #α := by rwa [← natCast_add_one_le_iff, ← Nat.cast_add_one]
  have := exists_notMem_of_length_lt [x, y] this
  simpa [not_or] using this

@[deprecated (since := "2026-02-17")] alias three_le := exists_ne_ne_of_three_le

/-! ### `powerlt` operation -/

/--
Definition of `powerlt` / `powerlt` 的定义

English:
definition powerlt
  signature: (a b : Cardinal.{u})
  body: ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

中文:
定义 powerlt
  签名: (a b : Cardinal.{u})
  定义体: ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

Depends on / 依赖: Cardinal
-/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

/--
theorem `le_powerlt` / 定理 `le_powerlt`

English:
theorem le_powerlt
  given: {b c : Cardinal.{u}} (a) (h : c < b)
  statement: (a ^ c) <= a ^< b
  proof: by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

中文:
定理 le_powerlt
  条件: {b c : Cardinal.{u}} (a) (h : c < b)
  结论: (a ^ c) <= a ^< b
  证明: by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

Depends on / 依赖: Cardinal, bddAbove_Iio, bddAbove_image, image_eq_range, le_ciSup
-/
theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a ^ c) <= a ^< b := by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

/--
theorem `powerlt_le` / 定理 `powerlt_le`

English:
theorem powerlt_le
  given: {a b c : Cardinal.{u}}
  statement: a ^< b <= c ↔ forall x < b, a ^ x <= c
  proof: by
  rw [powerlt]; rw [ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio

中文:
定理 powerlt_le
  条件: {a b c : Cardinal.{u}}
  结论: a ^< b <= c ↔ 对任意 x < b, a ^ x <= c
  证明: by
  rw [powerlt]; rw [ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio

Depends on / 依赖: bddAbove_Iio, bddAbove_image, ciSup_le_iff, image_eq_range, powerlt
-/
theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ forall x < b, a ^ x <= c := by
  rw [powerlt]; rw [ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio

/--
theorem `powerlt_le_powerlt_left` / 定理 `powerlt_le_powerlt_left`

English:
theorem powerlt_le_powerlt_left
  given: {a b c : Cardinal} (h : b <= c)
  statement: a ^< b <= a ^< c
  proof: powerlt_le.2 fun _ hx => le_powerlt a hx.trans_le h

中文:
定理 powerlt_le_powerlt_left
  条件: {a b c : Cardinal} (h : b <= c)
  结论: a ^< b <= a ^< c
  证明: powerlt_le.2 fun _ hx => le_powerlt a hx.trans_le h

Depends on / 依赖: hx.trans_le, le_powerlt, powerlt_le, trans_le
-/
theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b <= c) : a ^< b <= a ^< c :=
powerlt_le.2 fun _ hx => le_powerlt a hx.trans_le h

/--
theorem `powerlt_mono_left` / 定理 `powerlt_mono_left`

English:
theorem powerlt_mono_left
  given: (a)
  statement: Monotone fun c => a ^< c
  proof: fun _ _ => powerlt_le_powerlt_left

中文:
定理 powerlt_mono_left
  条件: (a)
  结论: Monotone fun c => a ^< c
  证明: fun _ _ => powerlt_le_powerlt_left

Depends on / 依赖: powerlt_le_powerlt_left
-/
theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun _ _ => powerlt_le_powerlt_left

/--
theorem `powerlt_succ` / 定理 `powerlt_succ`

English:
theorem powerlt_succ
  given: {a b : Cardinal} (h : a != 0)
  statement: a ^< succ b = a ^ b
  proof: (powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm
    le_powerlt a (lt_succ b)

中文:
定理 powerlt_succ
  条件: {a b : Cardinal} (h : a != 0)
  结论: a ^< succ b = a ^ b
  证明: (powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm
    le_powerlt a (lt_succ b)

Depends on / 依赖: antisymm, le_of_lt_succ, le_powerlt, lt_succ, power_le_power_left, powerlt_le
-/
theorem powerlt_succ {a b : Cardinal} (h : a != 0) : a ^< succ b = a ^ b :=
(powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm
    le_powerlt a (lt_succ b)

/--
theorem `powerlt_min` / 定理 `powerlt_min`

English:
theorem powerlt_min
  given: {a b c : Cardinal}
  statement: a ^< min b c = min (a ^< b) (a ^< c)
  proof: (powerlt_mono_left a).map_min

中文:
定理 powerlt_min
  条件: {a b c : Cardinal}
  结论: a ^< min b c = min (a ^< b) (a ^< c)
  证明: (powerlt_mono_left a).map_min

Depends on / 依赖: map_min, powerlt_mono_left
-/
theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min

/--
theorem `powerlt_max` / 定理 `powerlt_max`

English:
theorem powerlt_max
  given: {a b c : Cardinal}
  statement: a ^< max b c = max (a ^< b) (a ^< c)
  proof: (powerlt_mono_left a).map_max

中文:
定理 powerlt_max
  条件: {a b c : Cardinal}
  结论: a ^< max b c = max (a ^< b) (a ^< c)
  证明: (powerlt_mono_left a).map_max

Depends on / 依赖: map_max, powerlt_mono_left
-/
theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max

/--
theorem `zero_powerlt` / 定理 `zero_powerlt`

English:
theorem zero_powerlt
  given: {a : Cardinal} (h : a != 0)
  statement: 0 ^< a = 1
  proof: by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]

中文:
定理 zero_powerlt
  条件: {a : Cardinal} (h : a != 0)
  结论: 0 ^< a = 1
  证明: by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]

Depends on / 依赖: antisymm, le_powerlt, pos_iff_ne_zero, power_zero, powerlt_le, zero_power_le
-/
theorem zero_powerlt {a : Cardinal} (h : a != 0) : 0 ^< a = 1 := by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]
/--
theorem `powerlt_zero` / 定理 `powerlt_zero`

English:
theorem powerlt_zero
  given: {a : Cardinal}
  statement: a ^< 0 = 0
  proof: by
  convert! Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr not_lt_zero

中文:
定理 powerlt_zero
  条件: {a : Cardinal}
  结论: a ^< 0 = 0
  证明: by
  convert! Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr not_lt_zero

Depends on / 依赖: Cardinal, Cardinal.iSup_of_empty, Subtype, Subtype.isEmpty_of_false, convert, iSup_of_empty, isEmpty_of_false, mem_Iio, mem_Iio.not.mpr, not_lt_zero
-/
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert! Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr not_lt_zero

/--
theorem `_root_.WellFounded.cardinalMk_subtype_lt_min_compl_le` / 定理 `_root_.WellFounded.cardinalMk_subtype_lt_min_compl_le`

English:
theorem _root_.WellFounded.cardinalMk_subtype_lt_min_compl_le
  statement: {r : α -> α -> Prop}
  proof: Cardinal.mk_le_mk_of_subset fun _ => wf.mem_of_lt_min_compl

中文:
定理 _root_.WellFounded.cardinalMk_subtype_lt_min_compl_le
  结论: {r : α -> α -> 命题}
  证明: Cardinal.mk_le_mk_of_subset fun _ => wf.mem_of_lt_min_compl

Depends on / 依赖: Cardinal, Cardinal.mk_le_mk_of_subset, Real.isScalarTower, T2Space, TopologicalSpace, isScalarTower, mem_of_lt_min_compl, mk_le_mk_of_subset, wf.mem_of_lt_min_compl
-/
theorem _root_.WellFounded.cardinalMk_subtype_lt_min_compl_le {r : α -> α -> Prop}
    (wf : WellFounded r) {s : Set α} (hs : sᶜ.Nonempty) : #{ x // r x (wf.min sᶜ hs) } <= #s :=
  Cardinal.mk_le_mk_of_subset fun _ => wf.mem_of_lt_min_compl

end Cardinal
