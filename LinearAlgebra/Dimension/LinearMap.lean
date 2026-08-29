/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The rank of a linear map

## Main Definition
- `LinearMap.rank`: The rank of a linear map.
-/

public section


noncomputable section

universe u v v' v''

variable {K : Type u} {V V₁ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

open Cardinal Basis Submodule Function Set

namespace LinearMap

section Ring

variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid V₁] [Module K V₁]
variable [AddCommMonoid V'] [Module K V']

/--
Definition of `rank` / `rank` 的定义

English:
abbreviation rank
  signature: (f : V ->ₗ[K] V')
  body: Module.rank K (LinearMap.range f)

中文:
缩写 rank
  签名: (f : V ->ₗ[K] V')
  定义体: Module.rank K (LinearMap.range f)

Depends on / 依赖: LinearMap, LinearMap.range, Module, Module.rank
-/
abbrev rank (f : V ->ₗ[K] V') : Cardinal :=
  Module.rank K (LinearMap.range f)

/--
theorem `rank_le_range` / 定理 `rank_le_range`

English:
theorem rank_le_range
  given: (f : V ->ₗ[K] V')
  statement: rank f <= Module.rank K V'
  proof: Submodule.rank_le _

中文:
定理 rank_le_range
  条件: (f : V ->ₗ[K] V')
  结论: rank f <= 模.rank K V'
  证明: Submodule.rank_le _

Depends on / 依赖: Submodule, Submodule.rank_le, rank_le
-/
theorem rank_le_range (f : V ->ₗ[K] V') : rank f <= Module.rank K V' :=
  Submodule.rank_le _

/--
theorem `rank_le_domain` / 定理 `rank_le_domain`

English:
theorem rank_le_domain
  given: (f : V ->ₗ[K] V₁)
  statement: rank f <= Module.rank K V
  proof: rank_range_le _

@[simp]

中文:
定理 rank_le_domain
  条件: (f : V ->ₗ[K] V₁)
  结论: rank f <= 模.rank K V
  证明: rank_range_le _

@[simp]

Depends on / 依赖: rank_range_le
-/
theorem rank_le_domain (f : V ->ₗ[K] V₁) : rank f <= Module.rank K V :=
  rank_range_le _

@[simp]
/--
theorem `rank_zero` / 定理 `rank_zero`

English:
theorem rank_zero
  given: [Nontrivial K]
  statement: rank (0 : V ->ₗ[K] V') = 0
  proof: by
  rw [rank]; rw [LinearMap.range_zero]; rw [rank_bot]

中文:
定理 rank_zero
  条件: [非平凡 K]
  结论: rank (0 : V ->ₗ[K] V') = 0
  证明: by
  rw [rank]; rw [LinearMap.range_zero]; rw [rank_bot]

Depends on / 依赖: LinearMap, LinearMap.range_zero, range_zero, rank_bot
-/
theorem rank_zero [Nontrivial K] : rank (0 : V ->ₗ[K] V') = 0 := by
  rw [rank]; rw [LinearMap.range_zero]; rw [rank_bot]

variable [AddCommMonoid V''] [Module K V'']

/--
theorem `rank_comp_le_left` / 定理 `rank_comp_le_left`

English:
theorem rank_comp_le_left
  given: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  statement: rank (f.comp g) <= rank f
  proof: by
  refine Submodule.rank_mono ?_
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

中文:
定理 rank_comp_le_left
  条件: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  结论: rank (f.comp g) <= rank f
  证明: by
  refine Submodule.rank_mono ?_
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

Depends on / 依赖: LinearMap, LinearMap.map_le_range, LinearMap.range_comp, Submodule, Submodule.rank_mono, map_le_range, range_comp, rank_mono
-/
theorem rank_comp_le_left (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') : rank (f.comp g) <= rank f := by
  refine Submodule.rank_mono ?_
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

/--
theorem `lift_rank_comp_le_right` / 定理 `lift_rank_comp_le_right`

English:
theorem lift_rank_comp_le_right
  given: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  proof: by
  rw [rank]; rw [rank]; rw [LinearMap.range_comp]; exact lift_rank_map_le _ _

中文:
定理 lift_rank_comp_le_right
  条件: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  证明: by
  rw [rank]; rw [rank]; rw [LinearMap.range_comp]; exact lift_rank_map_le _ _

Depends on / 依赖: LinearMap, LinearMap.range_comp, lift_rank_map_le, range_comp
-/
theorem lift_rank_comp_le_right (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) <= Cardinal.lift.{v''} (rank g) := by
  rw [rank]; rw [rank]; rw [LinearMap.range_comp]; exact lift_rank_map_le _ _

/--
theorem `lift_rank_comp_le` / 定理 `lift_rank_comp_le`

English:
theorem lift_rank_comp_le
  given: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  proof: le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)

中文:
定理 lift_rank_comp_le
  条件: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'')
  证明: le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)

Depends on / 依赖: Cardinal, Cardinal.lift_le.mpr, le_min, lift_le, lift_rank_comp_le_right, rank_comp_le_left
-/
theorem lift_rank_comp_le (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) <=
      min (Cardinal.lift.{v'} (rank f)) (Cardinal.lift.{v''} (rank g)) :=
  le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)

variable [AddCommGroup V'₁] [Module K V'₁]

/--
theorem `rank_comp_le_right` / 定理 `rank_comp_le_right`

English:
theorem rank_comp_le_right
  given: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁)
  statement: rank (f.comp g) <= rank g
  proof: by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f

中文:
定理 rank_comp_le_right
  条件: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁)
  结论: rank (f.comp g) <= rank g
  证明: by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f

Depends on / 依赖: Cardinal, Cardinal.lift_id, hf.add, hg.neg, lift_id, lift_rank_comp_le_right, sub_eq_add_neg
-/
theorem rank_comp_le_right (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁) : rank (f.comp g) <= rank g := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f

/--
theorem `rank_comp_le` / 定理 `rank_comp_le`

English:
theorem rank_comp_le
  given: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁)
  proof: by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f

中文:
定理 rank_comp_le
  条件: (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁)
  证明: by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_id, lift_rank_comp_le
-/
theorem rank_comp_le (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁) :
    rank (f.comp g) <= min (rank f) (rank g) := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V'] [Module K V']

/--
theorem `rank_add_le` / 定理 `rank_add_le`

English:
theorem rank_add_le
  given: (f g : V ->ₗ[K] V')
  statement: rank (f + g) <= rank f + rank g
  proof: calc
    rank (f + g) <= Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine Submodule.rank_mono ?_
exact LinearMap.range_le_iff_comap.2 eq_top_iff'.2 fun x =>
        show f x + g x in (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_su

中文:
定理 rank_add_le
  条件: (f g : V ->ₗ[K] V')
  结论: rank (f + g) <= rank f + rank g
  证明: calc
    rank (f + g) <= Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine Submodule.rank_mono ?_
exact LinearMap.range_le_iff_comap.2 eq_top_iff'.2 fun x =>
        show f x + g x in (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_su

Depends on / 依赖: LinearMap, LinearMap.range, LinearMap.range_le_iff_comap, Module, Module.rank, Submodule, Submodule.rank_add_le_rank_add_rank, Submodule.rank_mono, eq_top_iff, mem_sup, range_le_iff_comap, rank_add_le_rank_add_rank, rank_mono
-/
theorem rank_add_le (f g : V ->ₗ[K] V') : rank (f + g) <= rank f + rank g :=
  calc
    rank (f + g) <= Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine Submodule.rank_mono ?_
exact LinearMap.range_le_iff_comap.2 eq_top_iff'.2 fun x =>
        show f x + g x in (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ <= rank f + rank g := Submodule.rank_add_le_rank_add_rank _ _

/--
theorem `rank_finsetSum_le` / 定理 `rank_finsetSum_le`

English:
theorem rank_finsetSum_le
  given: {η} (s : Finset η) (f : η -> V ->ₗ[K] V')
  proof: @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a <= b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (by gcongr)

@[deprecated (since := "2026-04-08")] alias rank_finset_sum_le := rank_finsetSum_le

中文:
定理 rank_finsetSum_le
  条件: {η} (s : 有限集 η) (f : η -> V ->ₗ[K] V')
  证明: @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a <= b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (by gcongr)

@[deprecated (since := "2026-04-08")] alias rank_finset_sum_le := rank_finsetSum_le

Depends on / 依赖: Finset, Finset.sum_hom_rel, le_of_eq, le_trans, rank_add_le, rank_zero, sum_hom_rel
-/
theorem rank_finsetSum_le {η} (s : Finset η) (f : η -> V ->ₗ[K] V') :
    rank (∑ d in s, f d) <= ∑ d in s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a <= b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (by gcongr)

@[deprecated (since := "2026-04-08")] alias rank_finset_sum_le := rank_finsetSum_le

/--
theorem `le_rank_iff_exists_linearIndependent` / 定理 `le_rank_iff_exists_linearIndependent`

English:
theorem le_rank_iff_exists_linearIndependent
  given: {c : Cardinal} {f : V ->ₗ[K] V'}
  proof: by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  refine ⟨fun h => ?_, ?_⟩
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    refine ⟨g '' s, Cardinal.mk

中文:
定理 le_rank_iff_存在_linearIndependent
  条件: {c : 基数} {f : V ->ₗ[K] V'}
  证明: by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  refine ⟨fun h => ?_, ?_⟩
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    refine ⟨g '' s, Cardinal.mk

Depends on / 依赖: Cardinal, Cardinal.mk_image_eq_lift, LeftInverse, LinearIndepOn, LinearMap, LinearMap.congr_fun, Subtype, Subtype.val, _root_, _root_.le_rank_iff_exists_linearIndependent, congr_arg, congr_fun, convert, exists_rightInverse_of_surjective, f.rangeRestrict, f.rangeRestrict.exists_rightInverse_of_surjective, f.range_rangeRestrict, fg.injective, injective, le_rank_iff_exists_linearIndependent
-/
theorem le_rank_iff_exists_linearIndependent {c : Cardinal} {f : V ->ₗ[K] V'} :
    c <= rank f ↔ exists s : Set V,
    Cardinal.lift.{v'} #s = Cardinal.lift.{v} c ∧ LinearIndepOn K f s := by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  refine ⟨fun h => ?_, ?_⟩
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    refine ⟨g '' s, Cardinal.mk_image_eq_lift _ _ fg.injective, ?_⟩
    replace fg : forall x, f (g x) = x := by
      intro x
      convert! congr_arg Subtype.val (fg x)
    replace si : LinearIndepOn K (fun x => f (g x)) s := by
      simpa only [fg] using! si.map' _ (ker_subtype _)
    exact si.image_of_comp
  · rintro ⟨s, hsc, si⟩
    have : LinearIndepOn K f.rangeRestrict s :=
      LinearIndependent.of_comp (LinearMap.range f).subtype (by convert! si)
    convert! this.id_image.cardinal_le_rank
    rw [← Cardinal.lift_inj]; rw [← hsc]; rw [Cardinal.mk_image_eq_of_injOn_lift]
    exact injOn_iff_injective.2 this.injective

/--
theorem `le_rank_iff_exists_linearIndependent_finset` / 定理 `le_rank_iff_exists_linearIndependent_finset`

English:
theorem le_rank_iff_exists_linearIndependent_finset
  given: {n : Nat} {f : V ->ₗ[K] V'}
  proof: by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

中文:
定理 le_rank_iff_存在_linearIndependent_finset
  条件: {n : 自然数} {f : V ->ₗ[K] V'}
  证明: by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

Depends on / 依赖: Cardinal, Cardinal.lift_eq_nat_iff, Cardinal.lift_natCast, Cardinal.mk_set_eq_nat_iff_finset, le_rank_iff_exists_linearIndependent, lift_eq_nat_iff, lift_natCast, mk_set_eq_nat_iff_finset
-/
theorem le_rank_iff_exists_linearIndependent_finset {n : Nat} {f : V ->ₗ[K] V'} :
    ↑n <= rank f ↔ exists s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

end DivisionRing

end LinearMap
