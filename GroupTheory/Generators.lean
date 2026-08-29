/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Group generators as data

## Main definitions

* `Group.Generators G ι`: The generators of a group are given by a generating family indexed by `ι`
and an assignment `val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`.

## Main results

* `Group.Generators.hom_ext`: if two homomorphisms coincide on the elements of a generating family,
  then they are equal.
* `Group.fg_iff_nonempty_finite_generators`: a group is finitely generated if and only if it
  admits a finite generating family.

## Implementation notes

* The index type `ι` is a parameter, not a field, following the pattern of `Algebra.Generators`.
* Unlike `Algebra.Generators`, this structure bundles no section of `FreeGroup.lift val`,
  it just bundles a proof of surjectivity.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017], §1

## Tags

group generators, generating set, finitely generated
-/

@[expose] public section

variable {G H ι ι' : Type*} [Group G] [Group H]

/--
Definition of `Group.Generators` / `Group.Generators` 的定义

English:
structure Group.Generators
  parameters: (G : Type*) [Group G] (ι : Type*)
  axioms and operations (2):
    - val : ι -> G
    - closure_eq_top : Subgroup.closure (Set.range val) = ⊤

中文:
结构 群.生成元
  参数: (G : 类型) [群 G] (ι : 类型)
  公理与运算 (2 个):
    - val : ι -> G
    - closure_eq_top : 子群.closure (集合.range val) = ⊤
-/
structure Group.Generators (G : Type*) [Group G] (ι : Type*) where
  /-- The generating family itself: `val i` is the element of `G` indexed by `i : ι`. -/
  val : ι -> G
  /-- The subgroup closure of the generators is the whole group. -/
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

namespace Group.Generators

variable (P : Group.Generators G ι)

/--
theorem `lift_val_surjective` / 定理 `lift_val_surjective`

English:
theorem lift_val_surjective
  statement: Function.Surjective (FreeGroup.lift P.val)
  proof: FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

中文:
定理 lift_val_surjective
  结论: 函数.满射 (自由群.lift P.val)
  证明: FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

Depends on / 依赖: FreeGroup, FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr, P.closure_eq_top, closure_eq_top, lift_surjective_iff_closure_range_eq_top
-/
theorem lift_val_surjective : Function.Surjective (FreeGroup.lift P.val) :=
  FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {M : Type*} [Monoid M] (f g : G ->* M) (h : forall i, f (P.val i) = g (P.val i))
  proof: MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

中文:
定理 hom_ext
  条件: {M : 类型} [幺半群 M] (f g : G ->* M) (h : 对任意 i, f (P.val i) = g (P.val i))
  证明: MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

Depends on / 依赖: MonoidHom, MonoidHom.eq_of_eqOn_dense, P.closure_eq_top, Set.forall_mem_range.mpr, closure_eq_top, eq_of_eqOn_dense, forall_mem_range
-/
theorem hom_ext {M : Type*} [Monoid M] (f g : G ->* M) (h : forall i, f (P.val i) = g (P.val i)) :
    f = g := MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: {S : Set G} (h : Subgroup.closure S = ⊤)
  body: Subtype.val
  closure_eq_top := by rwa [Subtype.range_coe]

@[simp]

中文:
定义 ofSet
  签名: {S : 集合 G} (h : 子群.closure S = ⊤)
  定义体: Subtype.val
  closure_eq_top := by rwa [Subtype.range_coe]

@[simp]

Depends on / 依赖: Subtype, Subtype.val
-/
def ofSet {S : Set G} (h : Subgroup.closure S = ⊤) : Group.Generators G S where
  val := Subtype.val
  closure_eq_top := by rwa [Subtype.range_coe]

@[simp]
/--
lemma `ofSet_val` / 引理 `ofSet_val`

English:
lemma ofSet_val
  given: {S : Set G} (hS : Subgroup.closure S = ⊤)
  proof: rfl

中文:
引理 ofSet_val
  条件: {S : 集合 G} (hS : 子群.closure S = ⊤)
  证明: rfl
-/
lemma ofSet_val {S : Set G} (hS : Subgroup.closure S = ⊤) :
    (Group.Generators.ofSet hS).val = Subtype.val :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : G ->* H) (hf : Function.Surjective f)
  body: f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp]; rw [← MonoidHom.map_closure]; rw [P.closure_eq_top]; rw [Subgroup.map_top_of_surjective f hf]

@[simp]

中文:
定义 map
  签名: (f : G ->* H) (hf : 函数.满射 f)
  定义体: f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp]; rw [← MonoidHom.map_closure]; rw [P.closure_eq_top]; rw [Subgroup.map_top_of_surjective f hf]

@[simp]
-/
protected def map (f : G ->* H) (hf : Function.Surjective f) : Group.Generators H ι where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp]; rw [← MonoidHom.map_closure]; rw [P.closure_eq_top]; rw [Subgroup.map_top_of_surjective f hf]

@[simp]
/--
lemma `map_val` / 引理 `map_val`

English:
lemma map_val
  given: (P : Group.Generators G ι) (f : G ->* H) (hf : Function.Surjective f)
  proof: rfl

中文:
引理 map_val
  条件: (P : 群.生成元 G ι) (f : G ->* H) (hf : 函数.满射 f)
  证明: rfl
-/
lemma map_val (P : Group.Generators G ι) (f : G ->* H) (hf : Function.Surjective f) :
    (P.map f hf).val = f ∘ P.val :=
  rfl

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : Group.Generators G ι) (e : ι' ≃ ι)
  body: P.val ∘ e
  closure_eq_top := by
    rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]; rw [P.closure_eq_top]

@[simp]

中文:
定义 reindex
  签名: (P : 群.生成元 G ι) (e : ι' ≃ ι)
  定义体: P.val ∘ e
  closure_eq_top := by
    rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]; rw [P.closure_eq_top]

@[simp]

Depends on / 依赖: P.val
-/
def reindex (P : Group.Generators G ι) (e : ι' ≃ ι) : Group.Generators G ι' where
  val := P.val ∘ e
  closure_eq_top := by
    rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]; rw [P.closure_eq_top]

@[simp]
/--
lemma `reindex_val` / 引理 `reindex_val`

English:
lemma reindex_val
  given: (P : Group.Generators G ι) (e : ι' ≃ ι)
  statement: (P.reindex e).val = P.val ∘ e
  proof: rfl

中文:
引理 reindex_val
  条件: (P : 群.生成元 G ι) (e : ι' ≃ ι)
  结论: (P.reindex e).val = P.val ∘ e
  证明: rfl
-/
lemma reindex_val (P : Group.Generators G ι) (e : ι' ≃ ι) : (P.reindex e).val = P.val ∘ e :=
  rfl

/--
theorem `fg` / 定理 `fg`

English:
theorem fg
  given: [Finite ι] (P : Group.Generators G ι)
  statement: Group.FG G
  proof: Group.fg_of_surjective P.lift_val_surjective

中文:
定理 fg
  条件: [有限 ι] (P : 群.生成元 G ι)
  结论: 群.FG G
  证明: Group.fg_of_surjective P.lift_val_surjective

Depends on / 依赖: Group.fg_of_surjective, P.lift_val_surjective, fg_of_surjective, lift_val_surjective
-/
theorem fg [Finite ι] (P : Group.Generators G ι) : Group.FG G :=
  Group.fg_of_surjective P.lift_val_surjective

end Group.Generators

/--
theorem `Group.fg_iff_nonempty_finite_generators` / 定理 `Group.fg_iff_nonempty_finite_generators`

English:
theorem Group.fg_iff_nonempty_finite_generators
  proof: by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg

中文:
定理 群.fg_iff_nonempty_finite_generators
  证明: by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg

Depends on / 依赖: Generators, Group.Generators.ofSet, P.fg, S.card, S.equivFin.symm, equivFin, reindex
-/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ exists n : Nat, Nonempty (Group.Generators G (Fin n)) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg
