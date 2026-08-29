/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Newell Jensen
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedGroup rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `toGroup f`: the canonical group homomorphism `PresentedGroup rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/

@[expose] public section


variable {α β : Type*}

/--
Definition of `PresentedGroup` / `PresentedGroup` 的定义

English:
definition PresentedGroup
  signature: (rels : Set (FreeGroup α))
  body: FreeGroup α ⧸ Subgroup.normalClosure rels
deriving Group

中文:
定义 PresentedGroup
  签名: (rels : 集合 (自由群 α))
  定义体: FreeGroup α ⧸ Subgroup.normalClosure rels
deriving Group

Depends on / 依赖: FreeGroup, Subgroup, Subgroup.normalClosure, normalClosure
-/
def PresentedGroup (rels : Set (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels
deriving Group

namespace PresentedGroup

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (rels : Set (FreeGroup α))
  body: ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩

中文:
定义 mk
  签名: (rels : 集合 (自由群 α))
  定义体: ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.mk
-/
def mk (rels : Set (FreeGroup α)) : FreeGroup α ->* PresentedGroup rels :=
  ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  given: (rels : Set (FreeGroup α))
  statement: Function.Surjective mk rels
  proof: QuotientGroup.mk_surjective

中文:
定理 mk_surjective
  条件: (rels : 集合 (自由群 α))
  结论: 函数.满射 mk rels
  证明: QuotientGroup.mk_surjective

Depends on / 依赖: QuotientGroup, QuotientGroup.mk_surjective, mk_surjective
-/
theorem mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective mk rels :=
  QuotientGroup.mk_surjective

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: {rels : Set (FreeGroup α)} (x : α)
  body: mk rels (FreeGroup.of x)

中文:
定义 of
  签名: {rels : 集合 (自由群 α)} (x : α)
  定义体: mk rels (FreeGroup.of x)

Depends on / 依赖: FreeGroup, FreeGroup.of
-/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  mk rels (FreeGroup.of x)

open Subgroup in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : FreeGroup α ->* FreeGroup β)
  body: QuotientGroup.map _ _ f
    ((comap_normalClosure_image_ge s f).trans
    (comap_mono (normalClosure_mono hst.image_subset)))

中文:
定义 map
  签名: (f : 自由群 α ->* 自由群 β)
  定义体: QuotientGroup.map _ _ f
    ((comap_normalClosure_image_ge s f).trans
    (comap_mono (normalClosure_mono hst.image_subset)))
-/
protected def map (f : FreeGroup α ->* FreeGroup β)
    {s : Set (FreeGroup α)} {t : Set (FreeGroup β)} (hst : s.MapsTo f t) :
    PresentedGroup s ->* PresentedGroup t :=
  QuotientGroup.map _ _ f
    ((comap_normalClosure_image_ge s f).trans
    (comap_mono (normalClosure_mono hst.image_subset)))

/--
lemma `mk_eq_one_iff` / 引理 `mk_eq_one_iff`

English:
lemma mk_eq_one_iff
  given: {rels : Set (FreeGroup α)} {x : FreeGroup α}
  proof: QuotientGroup.eq_one_iff _

中文:
引理 mk_eq_one_iff
  条件: {rels : 集合 (自由群 α)} {x : 自由群 α}
  证明: QuotientGroup.eq_one_iff _

Depends on / 依赖: QuotientGroup, QuotientGroup.eq_one_iff, eq_one_iff
-/
lemma mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} :
    mk rels x = 1 ↔ x in Subgroup.normalClosure rels :=
  QuotientGroup.eq_one_iff _

/--
lemma `one_of_mem` / 引理 `one_of_mem`

English:
lemma one_of_mem
  given: {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x in rels)
  proof: mk_eq_one_iff.mpr Subgroup.subset_normalClosure hx

中文:
引理 one_of_mem
  条件: {rels : 集合 (自由群 α)} {x : 自由群 α} (hx : x in rels)
  证明: mk_eq_one_iff.mpr Subgroup.subset_normalClosure hx

Depends on / 依赖: Subgroup, Subgroup.subset_normalClosure, mk_eq_one_iff, mk_eq_one_iff.mpr, subset_normalClosure
-/
lemma one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x in rels) :
    mk rels x = 1 :=
mk_eq_one_iff.mpr Subgroup.subset_normalClosure hx

/--
lemma `mk_eq_mk_of_mul_inv_mem` / 引理 `mk_eq_mk_of_mul_inv_mem`

English:
lemma mk_eq_mk_of_mul_inv_mem
  statement: {rels : Set (FreeGroup α)} {x y : FreeGroup α}
  proof: eq_of_mul_inv_eq_one one_of_mem hx

中文:
引理 mk_eq_mk_of_mul_inv_mem
  结论: {rels : 集合 (自由群 α)} {x y : 自由群 α}
  证明: eq_of_mul_inv_eq_one one_of_mem hx

Depends on / 依赖: eq_of_mul_inv_eq_one, one_of_mem
-/
lemma mk_eq_mk_of_mul_inv_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x * y⁻¹ in rels) : mk rels x = mk rels y :=
eq_of_mul_inv_eq_one one_of_mem hx

/--
lemma `mk_eq_mk_of_inv_mul_mem` / 引理 `mk_eq_mk_of_inv_mul_mem`

English:
lemma mk_eq_mk_of_inv_mul_mem
  statement: {rels : Set (FreeGroup α)} {x y : FreeGroup α}
  proof: eq_of_inv_mul_eq_one one_of_mem hx

中文:
引理 mk_eq_mk_of_inv_mul_mem
  结论: {rels : 集合 (自由群 α)} {x y : 自由群 α}
  证明: eq_of_inv_mul_eq_one one_of_mem hx

Depends on / 依赖: eq_of_inv_mul_eq_one, one_of_mem
-/
lemma mk_eq_mk_of_inv_mul_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x⁻¹ * y in rels) : mk rels x = mk rels y :=
eq_of_inv_mul_eq_one one_of_mem hx

set_option backward.isDefEq.respectTransparency false in
/-- The generators of a presented group generate the presented group. That is, the subgroup closure
of the set of generators equals `⊤`. -/
@[simp]
/--
theorem `closure_range_of` / 定理 `closure_range_of`

English:
theorem closure_range_of
  given: (rels : Set (FreeGroup α))
  proof: by
  have : (PresentedGroup.of : α -> PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this]; rw [Set.range_comp]; rw [← MonoidHom.map_closure (QuotientGroup.mk' _)]; rw [FreeGroup.closure_range_of]; rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.

中文:
定理 closure_range_of
  条件: (rels : 集合 (自由群 α))
  证明: by
  have : (PresentedGroup.of : α -> PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this]; rw [Set.range_comp]; rw [← MonoidHom.map_closure (QuotientGroup.mk' _)]; rw [FreeGroup.closure_range_of]; rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.

Depends on / 依赖: FreeGroup, FreeGroup.closure_range_of, FreeGroup.of, MonoidHom, MonoidHom.map_closure, MonoidHom.range_eq_map, MonoidHom.range_eq_top, PresentedGroup, PresentedGroup.of, QuotientGroup, QuotientGroup.mk, Set.range_comp, _surjective, closure_range_of, map_closure, range_comp, range_eq_map, range_eq_top
-/
theorem closure_range_of (rels : Set (FreeGroup α)) :
    Subgroup.closure (Set.range (PresentedGroup.of : α -> PresentedGroup rels)) = ⊤ := by
  have : (PresentedGroup.of : α -> PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this]; rw [Set.range_comp]; rw [← MonoidHom.map_closure (QuotientGroup.mk' _)]; rw [FreeGroup.closure_range_of]; rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)

@[induction_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {rels : Set (FreeGroup α)} {C : PresentedGroup rels -> Prop}
  proof: Quotient.inductionOn' x H

中文:
定理 induction_on
  结论: {rels : 集合 (自由群 α)} {C : PresentedGroup rels -> 命题}
  证明: Quotient.inductionOn' x H

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {rels : Set (FreeGroup α)} {C : PresentedGroup rels -> Prop}
    (x : PresentedGroup rels) (H : forall z, C (mk rels z)) : C x :=
  Quotient.inductionOn' x H

/--
theorem `generated_by` / 定理 `generated_by`

English:
theorem generated_by
  statement: (rels : Set (FreeGroup α)) (H : Subgroup (PresentedGroup rels))
  proof: by
  obtain ⟨z⟩ := x
  induction z
  · exact one_mem H
  · exact h _
  · exact (Subgroup.inv_mem_iff H).mpr (by assumption)
  rename_i h1 h2
  change QuotientGroup.mk _ in H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

中文:
定理 generated_by
  结论: (rels : 集合 (自由群 α)) (H : 子群 (PresentedGroup rels))
  证明: by
  obtain ⟨z⟩ := x
  induction z
  · exact one_mem H
  · exact h _
  · exact (Subgroup.inv_mem_iff H).mpr (by assumption)
  rename_i h1 h2
  change QuotientGroup.mk _ in H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

Depends on / 依赖: H.carrier, QuotientGroup, QuotientGroup.mk, QuotientGroup.mk_mul, Subgroup, Subgroup.inv_mem_iff, Subgroup.mul_mem, carrier, inv_mem_iff, mk_mul, mul_mem, one_mem, rename_i
-/
theorem generated_by (rels : Set (FreeGroup α)) (H : Subgroup (PresentedGroup rels))
    (h : forall j : α, PresentedGroup.of j in H) (x : PresentedGroup rels) : x in H := by
  obtain ⟨z⟩ := x
  induction z
  · exact one_mem H
  · exact h _
  · exact (Subgroup.inv_mem_iff H).mpr (by assumption)
  rename_i h1 h2
  change QuotientGroup.mk _ in H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `PresentedGroup rels` to `G`.
-/
variable {G : Type*} [Group G] {f : α -> G} {rels : Set (FreeGroup α)}

local notation "F" => FreeGroup.lift f

/--
theorem `closure_rels_subset_ker` / 定理 `closure_rels_subset_ker`

English:
theorem closure_rels_subset_ker
  given: (h : forall r in rels, FreeGroup.lift f r = 1)
  proof: Subgroup.normalClosure_le_normal fun x w => MonoidHom.mem_ker.2 (h x w)

中文:
定理 closure_rels_subset_ker
  条件: (h : 对任意 r in rels, 自由群.lift f r = 1)
  证明: Subgroup.normalClosure_le_normal fun x w => MonoidHom.mem_ker.2 (h x w)

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, Subgroup, Subgroup.normalClosure_le_normal, mem_ker, normalClosure_le_normal
-/
theorem closure_rels_subset_ker (h : forall r in rels, FreeGroup.lift f r = 1) :
    Subgroup.normalClosure rels <= MonoidHom.ker F :=
  Subgroup.normalClosure_le_normal fun x w => MonoidHom.mem_ker.2 (h x w)

/--
theorem `to_group_eq_one_of_mem_closure` / 定理 `to_group_eq_one_of_mem_closure`

English:
theorem to_group_eq_one_of_mem_closure
  given: (h : forall r in rels, FreeGroup.lift f r = 1)
  proof: fun _ w => MonoidHom.mem_ker.1 closure_rels_subset_ker h w

中文:
定理 to_group_eq_one_of_mem_closure
  条件: (h : 对任意 r in rels, 自由群.lift f r = 1)
  证明: fun _ w => MonoidHom.mem_ker.1 closure_rels_subset_ker h w

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, closure_rels_subset_ker, mem_ker
-/
theorem to_group_eq_one_of_mem_closure (h : forall r in rels, FreeGroup.lift f r = 1) :
    forall x in Subgroup.normalClosure rels, F x = 1 :=
fun _ w => MonoidHom.mem_ker.1 closure_rels_subset_ker h w

/--
Definition of `toGroup` / `toGroup` 的定义

English:
definition toGroup
  signature: (h : forall r in rels, FreeGroup.lift f r = 1)
  body: QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]

中文:
定义 toGroup
  签名: (h : 对任意 r in rels, 自由群.lift f r = 1)
  定义体: QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.lift, Subgroup, Subgroup.normalClosure, normalClosure, to_group_eq_one_of_mem_closure
-/
def toGroup (h : forall r in rels, FreeGroup.lift f r = 1) : PresentedGroup rels ->* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]
/--
theorem `toGroup.of` / 定理 `toGroup.of`

English:
theorem toGroup.of
  given: (h : forall r in rels, FreeGroup.lift f r = 1) {x : α}
  statement: toGroup h (of x) = f x
  proof: FreeGroup.lift_apply_of

中文:
定理 toGroup.of
  条件: (h : 对任意 r in rels, 自由群.lift f r = 1) {x : α}
  结论: toGroup h (of x) = f x
  证明: FreeGroup.lift_apply_of

Depends on / 依赖: FreeGroup, FreeGroup.lift_apply_of, lift_apply_of
-/
theorem toGroup.of (h : forall r in rels, FreeGroup.lift f r = 1) {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift_apply_of

/--
theorem `toGroup.unique` / 定理 `toGroup.unique`

English:
theorem toGroup.unique
  statement: (h : forall r in rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels ->* G)
  proof: by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ => FreeGroup.lift_unique (g.comp (QuotientGroup.mk' _)) hg

@[ext]

中文:
定理 toGroup.unique
  结论: (h : 对任意 r in rels, 自由群.lift f r = 1) (g : PresentedGroup rels ->* G)
  证明: by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ => FreeGroup.lift_unique (g.comp (QuotientGroup.mk' _)) hg

@[ext]

Depends on / 依赖: FreeGroup, FreeGroup.lift_unique, QuotientGroup, QuotientGroup.induction_on, QuotientGroup.mk, g.comp, induction_on, lift_unique
-/
theorem toGroup.unique (h : forall r in rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels ->* G)
    (hg : forall x : α, g (PresentedGroup.of x) = f x) : forall {x}, g x = toGroup h x := by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ => FreeGroup.lift_unique (g.comp (QuotientGroup.mk' _)) hg

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ ψ : PresentedGroup rels ->* G} (hx : forall (x : α), φ (.of x) = ψ (.of x))
  statement: φ = ψ
  proof: by
  unfold PresentedGroup
  ext
  apply hx

中文:
定理 ext
  条件: {φ ψ : PresentedGroup rels ->* G} (hx : 对任意 (x : α), φ (.of x) = ψ (.of x))
  结论: φ = ψ
  证明: by
  unfold PresentedGroup
  ext
  apply hx

Depends on / 依赖: PresentedGroup
-/
theorem ext {φ ψ : PresentedGroup rels ->* G} (hx : forall (x : α), φ (.of x) = ψ (.of x)) : φ = ψ := by
  unfold PresentedGroup
  ext
  apply hx

/--
Definition of `equivPresentedGroup` / `equivPresentedGroup` 的定义

English:
definition equivPresentedGroup
  signature: (rels : Set (FreeGroup α)) (e : α ≃ β)
  body: QuotientGroup.congr (Subgroup.normalClosure rels)
    (Subgroup.normalClosure ((FreeGroup.freeGroupCongr e) '' rels)) (FreeGroup.freeGroupCongr e)
    (Subgroup.map_normalClosure rels (FreeGroup.freeGroupCongr e).toMonoidHom
      (FreeGroup.freeGroupCongr e).surjective)

中文:
定义 equivPresentedGroup
  签名: (rels : 集合 (自由群 α)) (e : α ≃ β)
  定义体: QuotientGroup.congr (Subgroup.normalClosure rels)
    (Subgroup.normalClosure ((FreeGroup.freeGroupCongr e) '' rels)) (FreeGroup.freeGroupCongr e)
    (Subgroup.map_normalClosure rels (FreeGroup.freeGroupCongr e).toMonoidHom
      (FreeGroup.freeGroupCongr e).surjective)

Depends on / 依赖: FreeGroup, FreeGroup.freeGroupCongr, QuotientGroup, QuotientGroup.congr, Subgroup, Subgroup.map_normalClosure, Subgroup.normalClosure, freeGroupCongr, map_normalClosure, normalClosure, surjective, toMonoidHom
-/
def equivPresentedGroup (rels : Set (FreeGroup α)) (e : α ≃ β) :
    PresentedGroup rels ≃* PresentedGroup (FreeGroup.freeGroupCongr e '' rels) :=
  QuotientGroup.congr (Subgroup.normalClosure rels)
    (Subgroup.normalClosure ((FreeGroup.freeGroupCongr e) '' rels)) (FreeGroup.freeGroupCongr e)
    (Subgroup.map_normalClosure rels (FreeGroup.freeGroupCongr e).toMonoidHom
      (FreeGroup.freeGroupCongr e).surjective)

/--
theorem `equivPresentedGroup_apply_of` / 定理 `equivPresentedGroup_apply_of`

English:
theorem equivPresentedGroup_apply_of
  given: (x : α) (rels : Set (FreeGroup α)) (e : α ≃ β)
  proof: rfl

中文:
定理 equivPresentedGroup_apply_of
  条件: (x : α) (rels : 集合 (自由群 α)) (e : α ≃ β)
  证明: rfl

Depends on / 依赖: FreeGroup, FreeGroup.freeGroupCongr, freeGroupCongr
-/
theorem equivPresentedGroup_apply_of (x : α) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    equivPresentedGroup rels e (PresentedGroup.of x) =
      PresentedGroup.of (rels := FreeGroup.freeGroupCongr e '' rels) (e x) := rfl

/--
theorem `equivPresentedGroup_symm_apply_of` / 定理 `equivPresentedGroup_symm_apply_of`

English:
theorem equivPresentedGroup_symm_apply_of
  given: (x : β) (rels : Set (FreeGroup α)) (e : α ≃ β)
  proof: rfl

中文:
定理 equivPresentedGroup_symm_apply_of
  条件: (x : β) (rels : 集合 (自由群 α)) (e : α ≃ β)
  证明: rfl

Depends on / 依赖: e.symm
-/
theorem equivPresentedGroup_symm_apply_of (x : β) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    (equivPresentedGroup rels e).symm (PresentedGroup.of x) =
      PresentedGroup.of (rels := rels) (e.symm x) := rfl

end ToGroup

instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

section Coprod

variable (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β))

/--
Definition of `toCoprod` / `toCoprod` 的定义

English:
definition toCoprod
  signature: : α oplus β -> Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂)
  body: Sum.elim (Monoid.Coprod.inl ∘ .of) (Monoid.Coprod.inr ∘ .of)

@[simp]

中文:
定义 toCoprod
  签名: : α oplus β -> 幺半群.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂)
  定义体: Sum.elim (Monoid.Coprod.inl ∘ .of) (Monoid.Coprod.inr ∘ .of)

@[simp]

Depends on / 依赖: Coprod, Monoid, Monoid.Coprod.inl, Monoid.Coprod.inr, Sum.elim
-/
def toCoprod : α oplus β -> Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂) :=
  Sum.elim (Monoid.Coprod.inl ∘ .of) (Monoid.Coprod.inr ∘ .of)

@[simp]
/--
lemma `lift_toCoprod_inl_eq_inl_mk` / 引理 `lift_toCoprod_inl_eq_inl_mk`

English:
lemma lift_toCoprod_inl_eq_inl_mk
  statement: (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
  proof: FreeGroup.ext_hom _ _ fun _ => rfl

@[simp]

中文:
引理 lift_toCoprod_inl_eq_inl_mk
  结论: (自由群.lift (toCoprod rels₁ rels₂)).comp
  证明: FreeGroup.ext_hom _ _ fun _ => rfl

@[simp]

Depends on / 依赖: FreeGroup, FreeGroup.ext_hom, ext_hom
-/
lemma lift_toCoprod_inl_eq_inl_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
    (FreeGroup.map Sum.inl) = Monoid.Coprod.inl.comp (mk rels₁) :=
  FreeGroup.ext_hom _ _ fun _ => rfl

@[simp]
/--
lemma `lift_toCoprod_inr_eq_inr_mk` / 引理 `lift_toCoprod_inr_eq_inr_mk`

English:
lemma lift_toCoprod_inr_eq_inr_mk
  statement: (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
  proof: FreeGroup.ext_hom _ _ fun _ => rfl

中文:
引理 lift_toCoprod_inr_eq_inr_mk
  结论: (自由群.lift (toCoprod rels₁ rels₂)).comp
  证明: FreeGroup.ext_hom _ _ fun _ => rfl

Depends on / 依赖: FreeGroup, FreeGroup.ext_hom, ext_hom
-/
lemma lift_toCoprod_inr_eq_inr_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
    (FreeGroup.map Sum.inr) = Monoid.Coprod.inr.comp (mk rels₂) :=
  FreeGroup.ext_hom _ _ fun _ => rfl

/--
lemma `lift_toCoprod_eq_one` / 引理 `lift_toCoprod_eq_one`

English:
lemma lift_toCoprod_eq_one
  statement: (r : FreeGroup (α oplus β))
  proof: by
  obtain ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ := hr <;> simp [← MonoidHom.comp_apply, one_of_mem hr]

中文:
引理 lift_toCoprod_eq_one
  结论: (r : 自由群 (α oplus β))
  证明: by
  obtain ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ := hr <;> simp [← MonoidHom.comp_apply, one_of_mem hr]

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, comp_apply, one_of_mem
-/
lemma lift_toCoprod_eq_one (r : FreeGroup (α oplus β))
    (hr : r in FreeGroup.map Sum.inl '' rels₁ union FreeGroup.map Sum.inr '' rels₂) :
    FreeGroup.lift (toCoprod rels₁ rels₂) r = 1 := by
  obtain ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ := hr <;> simp [← MonoidHom.comp_apply, one_of_mem hr]

/--
Definition of `coprodPresentations` / `coprodPresentations` 的定义

English:
definition coprodPresentations
  signature: :
  body: MonoidHom.toMulEquiv
    (toGroup (lift_toCoprod_eq_one rels₁ rels₂))
    (Monoid.Coprod.lift
      (PresentedGroup.map (FreeGroup.map Sum.inl) fun r hr => .inl ⟨r, hr, rfl⟩)
      (PresentedGroup.map (FreeGroup.map Sum.inr) fun r hr => .inr ⟨r, hr, rfl⟩))
    (ext <| Sum.rec (fun _ => rfl) (fun _ =

中文:
定义 coprodPresentations
  签名: :
  定义体: MonoidHom.toMulEquiv
    (toGroup (lift_toCoprod_eq_one rels₁ rels₂))
    (Monoid.Coprod.lift
      (PresentedGroup.map (FreeGroup.map Sum.inl) fun r hr => .inl ⟨r, hr, rfl⟩)
      (PresentedGroup.map (FreeGroup.map Sum.inr) fun r hr => .inr ⟨r, hr, rfl⟩))
    (ext <| Sum.rec (fun _ => rfl) (fun _ =

Depends on / 依赖: Coprod, FreeGroup, FreeGroup.map, Monoid, Monoid.Coprod.hom_ext, Monoid.Coprod.lift, MonoidHom, MonoidHom.toMulEquiv, PresentedGroup, PresentedGroup.map, Sum.inl, Sum.inr, Sum.rec, hom_ext, lift_toCoprod_eq_one, toGroup, toMulEquiv
-/
def coprodPresentations :
    PresentedGroup (FreeGroup.map Sum.inl '' rels₁ union FreeGroup.map Sum.inr '' rels₂) ≃*
    Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂) :=
  MonoidHom.toMulEquiv
    (toGroup (lift_toCoprod_eq_one rels₁ rels₂))
    (Monoid.Coprod.lift
      (PresentedGroup.map (FreeGroup.map Sum.inl) fun r hr => .inl ⟨r, hr, rfl⟩)
      (PresentedGroup.map (FreeGroup.map Sum.inr) fun r hr => .inr ⟨r, hr, rfl⟩))
    (ext <| Sum.rec (fun _ => rfl) (fun _ => rfl))
    (Monoid.Coprod.hom_ext (ext fun _ => rfl) (ext fun _ => rfl))
end Coprod
end PresentedGroup
