/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices

/-!
# Simplices that are uniquely codimensional one faces

Let `X` be a simplicial set. If `x : X _⦋d⦌` and `y : X _⦋d + 1⦌`,
we say that `x` is uniquely a `1`-codimensional face of `y` if there
exists a unique `i : Fin (d + 2)` such that `X.δ i y = x`. In this file,
we extend this to a predicate `IsUniquelyCodimOneFace` involving two terms
in the type `X.S` of simplices of `X`. This is used in the
file `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean` for the
study of strong (inner) anodyne extensions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.S

variable {X : SSet.{u}} (x y : X.S)

/--
Definition of `IsUniquelyCodimOneFace` / `IsUniquelyCodimOneFace` 的定义

English:
definition IsUniquelyCodimOneFace
  signature: : Prop
  body: y.dim = x.dim + 1 ∧ exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

中文:
定义 IsUniquelyCodimOneFace
  签名: : 命题
  定义体: y.dim = x.dim + 1 ∧ exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

Depends on / 依赖: X.map, f.op, simplex, x.dim, x.simplex, y.dim, y.simplex
-/
def IsUniquelyCodimOneFace : Prop :=
  y.dim = x.dim + 1 ∧ exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

namespace IsUniquelyCodimOneFace

/--
lemma `iff` / 引理 `iff`

English:
lemma iff
  given: {d : Nat} (x : X _⦋d⦌) (y : X _⦋d + 1⦌)
  proof: by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj => SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ => ?_⟩
    ob

中文:
引理 iff
  条件: {d : 自然数} (x : X _⦋d⦌) (y : X _⦋d + 1⦌)
  证明: by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj => SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ => ?_⟩
    ob

Depends on / 依赖: SimplexCategory, SimplexCategory.eq_
-/
lemma iff {d : Nat} (x : X _⦋d⦌) (y : X _⦋d + 1⦌) :
    IsUniquelyCodimOneFace (S.mk x) (S.mk y) ↔
      exists! (i : Fin (d + 2)), X.δ i y = x := by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj => SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ => ?_⟩
    obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl : j = i := h₂ _ h₄
    rfl

variable {x y} (hxy : IsUniquelyCodimOneFace x y)

include hxy in
/--
lemma `dim_eq` / 引理 `dim_eq`

English:
lemma dim_eq
  statement: y.dim = x.dim + 1
  proof: hxy.1

中文:
引理 dim_eq
  结论: y.dim = x.dim + 1
  证明: hxy.1
-/
lemma dim_eq : y.dim = x.dim + 1 := hxy.1

section

variable {d : Nat} (hd : x.dim = d)

/--
lemma `cast` / 引理 `cast`

English:
lemma cast
  statement: IsUniquelyCodimOneFace (x.cast hd) (y.cast (d := d + 1) (by rw [hxy.dim_eq, hd]))
  proof: by
  simpa only [cast_eq_self]

中文:
引理 cast
  结论: IsUniquelyCodimOneFace (x.cast hd) (y.cast (d := d + 1) (by rw [hxy.dim_eq, hd]))
  证明: by
  simpa only [cast_eq_self]

Depends on / 依赖: cast_eq_self, dim_eq, hxy.dim_eq
-/
lemma cast : IsUniquelyCodimOneFace (x.cast hd) (y.cast (d := d + 1) (by rw [hxy.dim_eq, hd])) := by
  simpa only [cast_eq_self]

/--
lemma `existsUnique_δ_cast_simplex` / 引理 `existsUnique_δ_cast_simplex`

English:
lemma existsUnique_δ_cast_simplex
  proof: by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in

中文:
引理 existsUnique_δ_cast_simplex
  证明: by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in

Depends on / 依赖: S.cast, hxy.cast
-/
lemma existsUnique_δ_cast_simplex :
    exists! (i : Fin (d + 2)), X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex =
      (x.cast hd).simplex := by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in
/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: : Fin (d + 2)
  body: (hxy.existsUnique_δ_cast_simplex hd).exists.choose

中文:
定义 index
  签名: : Fin (d + 2)
  定义体: (hxy.existsUnique_δ_cast_simplex hd).exists.choose

Depends on / 依赖: exists.choose, hxy.existsUnique_
-/
noncomputable def index : Fin (d + 2) :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose

/--
lemma `δ_index` / 引理 `δ_index`

English:
lemma δ_index
  proof: (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec

中文:
引理 δ_index
  证明: (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec

Depends on / 依赖: choose_spec, exists.choose_spec, hxy.existsUnique_
-/
lemma δ_index :
    X.δ (hxy.index hd) (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec

/--
lemma `δ_eq_iff` / 引理 `δ_eq_iff`

English:
lemma δ_eq_iff
  given: (i : Fin (d + 2))
  proof: ⟨fun h => (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

include hxy in

中文:
引理 δ_eq_iff
  条件: (i : Fin (d + 2))
  证明: ⟨fun h => (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

include hxy in

Depends on / 依赖: hxy.existsUnique_, unique
-/
lemma δ_eq_iff (i : Fin (d + 2)) :
    X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔
      i = hxy.index hd :=
  ⟨fun h => (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

include hxy in
/--
lemma `le` / 引理 `le`

English:
lemma le
  statement: x <= y
  proof: by
  have := hxy.δ_index rfl
  simp only [cast_simplex_rfl] at this
  rw [S.le_def]; rw [← y.subcomplex_cast hxy.dim_eq]; rw [Subfunctor.ofSection_le_iff]; rw [← this]
  exact ⟨(SimplexCategory.δ _).op, rfl⟩

中文:
引理 le
  结论: x <= y
  证明: by
  have := hxy.δ_index rfl
  simp only [cast_simplex_rfl] at this
  rw [S.le_def]; rw [← y.subcomplex_cast hxy.dim_eq]; rw [Subfunctor.ofSection_le_iff]; rw [← this]
  exact ⟨(SimplexCategory.δ _).op, rfl⟩

Depends on / 依赖: S.le_def, SimplexCategory, Subfunctor, Subfunctor.ofSection_le_iff, cast_simplex_rfl, dim_eq, hxy.dim_eq, le_def, ofSection_le_iff, subcomplex_cast, y.subcomplex_cast
-/
lemma le : x <= y := by
  have := hxy.δ_index rfl
  simp only [cast_simplex_rfl] at this
  rw [S.le_def]; rw [← y.subcomplex_cast hxy.dim_eq]; rw [Subfunctor.ofSection_le_iff]; rw [← this]
  exact ⟨(SimplexCategory.δ _).op, rfl⟩

set_option backward.defeqAttrib.useBackward true in
include hxy in
/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  statement: (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
  proof: (hxy.cast hd).2.unique ⟨by dsimp; infer_instance, hf⟩
    ⟨by dsimp; infer_instance, hxy.δ_index hd⟩

中文:
引理 unique
  结论: (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
  证明: (hxy.cast hd).2.unique ⟨by dsimp; infer_instance, hf⟩
    ⟨by dsimp; infer_instance, hxy.δ_index hd⟩

Depends on / 依赖: hxy.cast, infer_instance, unique
-/
lemma unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
    (hf : X.map f.op (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex) :
    f = SimplexCategory.δ (hxy.index hd) :=
  (hxy.cast hd).2.unique ⟨by dsimp; infer_instance, hf⟩
    ⟨by dsimp; infer_instance, hxy.δ_index hd⟩

end

set_option backward.isDefEq.respectTransparency.types false in
include hxy in
/--
lemma `op` / 引理 `op`

English:
lemma op
  statement: (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y)
  proof: by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  simp only [opEquiv_symm_apply, iff]
  refine ⟨(hxy.index rfl).rev, by simpa using hxy.δ_index rfl, fun i hi => ?_⟩
  obtain ⟨i, rfl⟩ := i.rev_surjective
  simpa [← hxy.δ_eq_i

中文:
引理 op
  结论: (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y)
  证明: by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  simp only [opEquiv_symm_apply, iff]
  refine ⟨(hxy.index rfl).rev, by simpa using hxy.δ_index rfl, fun i hi => ?_⟩
  obtain ⟨i, rfl⟩ := i.rev_surjective
  simpa [← hxy.δ_eq_i

Depends on / 依赖: dim_eq, hxy.dim_eq, hxy.index, i.rev_surjective, mk_surjective, opEquiv_symm_apply, rev_surjective, x.mk_surjective, y.mk_surjective
-/
lemma op : (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  simp only [opEquiv_symm_apply, iff]
  refine ⟨(hxy.index rfl).rev, by simpa using hxy.δ_index rfl, fun i hi => ?_⟩
  obtain ⟨i, rfl⟩ := i.rev_surjective
  simpa [← hxy.δ_eq_iff rfl] using hi

set_option backward.defeqAttrib.useBackward true in
include hxy in
/--
lemma `of_iso` / 引理 `of_iso`

English:
lemma of_iso
  given: {Y : SSet.{u}} (e : X ≅ Y)
  proof: by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  rw [iff] at hxy ⊢
  simpa [← SSet.δ_naturality_apply, dsimp% (e.app (Opposite.op ⦋d⦌)).toEquiv.apply_eq_iff_eq]

中文:
引理 of_iso
  条件: {Y : SSet.{u}} (e : X ≅ Y)
  证明: by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  rw [iff] at hxy ⊢
  simpa [← SSet.δ_naturality_apply, dsimp% (e.app (Opposite.op ⦋d⦌)).toEquiv.apply_eq_iff_eq]

Depends on / 依赖: Opposite, Opposite.op, apply_eq_iff_eq, dim_eq, e.app, hxy.dim_eq, mk_surjective, toEquiv, toEquiv.apply_eq_iff_eq, x.mk_surjective, y.mk_surjective
-/
lemma of_iso {Y : SSet.{u}} (e : X ≅ Y) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  rw [iff] at hxy ⊢
  simpa [← SSet.δ_naturality_apply, dsimp% (e.app (Opposite.op ⦋d⦌)).toEquiv.apply_eq_iff_eq]

/--
lemma `iff_of_iso` / 引理 `iff_of_iso`

English:
lemma iff_of_iso
  given: {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S)
  proof: ⟨fun hxy' => by simpa using hxy'.of_iso e.symm, fun hxy => hxy.of_iso e⟩

中文:
引理 iff_of_iso
  条件: {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S)
  证明: ⟨fun hxy' => by simpa using hxy'.of_iso e.symm, fun hxy => hxy.of_iso e⟩

Depends on / 依赖: e.symm, hxy.of_iso, of_iso
-/
lemma iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) ↔
      x.IsUniquelyCodimOneFace y :=
  ⟨fun hxy' => by simpa using hxy'.of_iso e.symm, fun hxy => hxy.of_iso e⟩

/--
lemma `index_of_iso` / 引理 `index_of_iso`

English:
lemma index_of_iso
  given: {Y : SSet.{u}} (e : X ≅ Y) {d : Nat} (hd : x.dim = d)
  proof: by
  obtain ⟨dx, x, rfl⟩ := x.mk_surjective
  obtain ⟨dy, y, rfl⟩ := y.mk_surjective
  obtain rfl : dy = dx + 1 := hxy.dim_eq
  obtain rfl : dx = d := hd
  symm
  simp [← (hxy.of_iso e).δ_eq_iff rfl,
    ← SSet.δ_naturality_apply, dsimp% hxy.δ_index rfl]

中文:
引理 index_of_iso
  条件: {Y : SSet.{u}} (e : X ≅ Y) {d : 自然数} (hd : x.dim = d)
  证明: by
  obtain ⟨dx, x, rfl⟩ := x.mk_surjective
  obtain ⟨dy, y, rfl⟩ := y.mk_surjective
  obtain rfl : dy = dx + 1 := hxy.dim_eq
  obtain rfl : dx = d := hd
  symm
  simp [← (hxy.of_iso e).δ_eq_iff rfl,
    ← SSet.δ_naturality_apply, dsimp% hxy.δ_index rfl]

Depends on / 依赖: dim_eq, hxy.dim_eq, hxy.of_iso, mk_surjective, of_iso, x.mk_surjective, y.mk_surjective
-/
lemma index_of_iso {Y : SSet.{u}} (e : X ≅ Y) {d : Nat} (hd : x.dim = d) :
    (hxy.of_iso e).index hd = hxy.index hd := by
  obtain ⟨dx, x, rfl⟩ := x.mk_surjective
  obtain ⟨dy, y, rfl⟩ := y.mk_surjective
  obtain rfl : dy = dx + 1 := hxy.dim_eq
  obtain rfl : dx = d := hd
  symm
  simp [← (hxy.of_iso e).δ_eq_iff rfl,
    ← SSet.δ_naturality_apply, dsimp% hxy.δ_index rfl]

end IsUniquelyCodimOneFace

end SSet.S
