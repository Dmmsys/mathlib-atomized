/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The preordered type of simplices of a simplicial set

In this file, we define the type `X.S` of simplices of a simplicial set `X`,
where a simplex consists of the data of `dim : ℕ` and `simplex : X _⦋dim⦌`.
We endow this type with a preorder defined by
`x ≤ y ↔ Subcomplex.ofSimplex x.simplex ≤ Subcomplex.ofSimplex y.simplex`.
In particular, as a preordered type, `X.S` is a category, but this is
not what is called "the category of simplices of `X`" in the literature
(and which is `X.Elementsᵒᵖ` in mathlib).

## TODO (@joelriou)

* Extend the `S` structure to define the type of nondegenerate
  simplices of a simplicial set `X`, and also the type of nondegenerate
  simplices of a simplicial set `X` which do not belong to a given subcomplex.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

/--
Definition of `S` / `S` 的定义

English:
structure S
  parameters: where
  axioms and operations (2):
    - {dim : Nat}
    - simplex : X _⦋dim⦌

中文:
结构 S
  参数: where
  公理与运算 (2 个):
    - {dim : 自然数}
    - simplex : X _⦋dim⦌
-/
structure S where
  /-- the dimension of the simplex -/
  {dim : Nat}
  /-- the simplex -/
  simplex : X _⦋dim⦌

variable {X}

namespace S

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (s : X.S)
  proof: ⟨s.dim, s.simplex, rfl⟩

中文:
引理 mk_surjective
  条件: (s : X.S)
  证明: ⟨s.dim, s.simplex, rfl⟩

Depends on / 依赖: s.dim, s.simplex, simplex
-/
lemma mk_surjective (s : X.S) :
    exists (n : Nat) (x : X _⦋n⦌), s = mk x :=
  ⟨s.dim, s.simplex, rfl⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S)
  body: S.mk (f.app _ s.simplex)

中文:
定义 map
  签名: {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S)
  定义体: S.mk (f.app _ s.simplex)

Depends on / 依赖: S.mk, f.app, s.simplex, simplex
-/
def map {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : Y.S :=
  S.mk (f.app _ s.simplex)

/--
lemma `dim_eq_of_eq` / 引理 `dim_eq_of_eq`

English:
lemma dim_eq_of_eq
  given: {s t : X.S} (h : s = t)
  proof: congr_arg dim h

中文:
引理 dim_eq_of_eq
  条件: {s t : X.S} (h : s = t)
  证明: congr_arg dim h

Depends on / 依赖: congr_arg
-/
lemma dim_eq_of_eq {s t : X.S} (h : s = t) :
    s.dim = t.dim :=
  congr_arg dim h

/--
lemma `dim_eq_of_mk_eq` / 引理 `dim_eq_of_mk_eq`

English:
lemma dim_eq_of_mk_eq
  statement: {n m : Nat} {x : X _⦋n⦌} {y : X _⦋m⦌}
  proof: dim_eq_of_eq h

中文:
引理 dim_eq_of_mk_eq
  结论: {n m : 自然数} {x : X _⦋n⦌} {y : X _⦋m⦌}
  证明: dim_eq_of_eq h

Depends on / 依赖: dim_eq_of_eq
-/
lemma dim_eq_of_mk_eq {n m : Nat} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  dim_eq_of_eq h

section

variable (s : X.S) {d : Nat} (hd : s.dim = d)

/-- When `s : X.S` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
@[simps dim]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: : X.S where
  body: d
  simplex := _root_.cast (by simp only [hd]) s.simplex

中文:
定义 cast
  签名: : X.S where
  定义体: d
  simplex := _root_.cast (by simp only [hd]) s.simplex
-/
def cast : X.S where
  dim := d
  simplex := _root_.cast (by simp only [hd]) s.simplex

/--
lemma `cast_eq_self` / 引理 `cast_eq_self`

English:
lemma cast_eq_self
  statement: s.cast hd = s
  proof: by
  obtain ⟨d, _, rfl⟩ := s.mk_surjective
  obtain rfl := hd
  rfl

@[simp]

中文:
引理 cast_eq_self
  结论: s.cast hd = s
  证明: by
  obtain ⟨d, _, rfl⟩ := s.mk_surjective
  obtain rfl := hd
  rfl

@[simp]

Depends on / 依赖: mk_surjective, s.mk_surjective
-/
lemma cast_eq_self : s.cast hd = s := by
  obtain ⟨d, _, rfl⟩ := s.mk_surjective
  obtain rfl := hd
  rfl

@[simp]
/--
lemma `cast_simplex_rfl` / 引理 `cast_simplex_rfl`

English:
lemma cast_simplex_rfl
  statement: (s.cast rfl).simplex = s.simplex
  proof: rfl

中文:
引理 cast_simplex_rfl
  结论: (s.cast rfl).simplex = s.simplex
  证明: rfl
-/
lemma cast_simplex_rfl : (s.cast rfl).simplex = s.simplex := rfl

end

/--
lemma `ext_iff'` / 引理 `ext_iff'`

English:
lemma ext_iff'
  given: (s t : X.S)
  proof: ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => by
    obtain ⟨_, _, rfl⟩ := s.mk_surjective
    obtain ⟨_, _, rfl⟩ := t.mk_surjective
    aesop⟩

中文:
引理 ext_iff'
  条件: (s t : X.S)
  证明: ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => by
    obtain ⟨_, _, rfl⟩ := s.mk_surjective
    obtain ⟨_, _, rfl⟩ := t.mk_surjective
    aesop⟩

Depends on / 依赖: mk_surjective, s.mk_surjective, t.mk_surjective
-/
lemma ext_iff' (s t : X.S) :
    s = t ↔ exists (h : s.dim = t.dim), (s.cast h).simplex = t.simplex :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => by
    obtain ⟨_, _, rfl⟩ := s.mk_surjective
    obtain ⟨_, _, rfl⟩ := t.mk_surjective
    aesop⟩

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: {n : Nat} (x y : X _⦋n⦌)
  proof: by
  simp

中文:
引理 ext_iff
  条件: {n : 自然数} (x y : X _⦋n⦌)
  证明: by
  simp
-/
lemma ext_iff {n : Nat} (x y : X _⦋n⦌) :
    S.mk x = S.mk y ↔ x = y := by
  simp

/--
Definition of `subcomplex` / `subcomplex` 的定义

English:
abbreviation subcomplex
  signature: (s : X.S)
  body: Subcomplex.ofSimplex s.simplex

中文:
缩写 subcomplex
  签名: (s : X.S)
  定义体: Subcomplex.ofSimplex s.simplex

Depends on / 依赖: Subcomplex, Subcomplex.ofSimplex, ofSimplex, s.simplex, simplex
-/
abbrev subcomplex (s : X.S) : X.Subcomplex := Subcomplex.ofSimplex s.simplex

/--
lemma `ofSimplex_eq_subcomplex_mk` / 引理 `ofSimplex_eq_subcomplex_mk`

English:
lemma ofSimplex_eq_subcomplex_mk
  given: {n : Nat} (x : X _⦋n⦌)
  proof: rfl

@[simp]

中文:
引理 ofSimplex_eq_subcomplex_mk
  条件: {n : 自然数} (x : X _⦋n⦌)
  证明: rfl

@[simp]
-/
lemma ofSimplex_eq_subcomplex_mk {n : Nat} (x : X _⦋n⦌) :
    Subcomplex.ofSimplex x = (S.mk x).subcomplex := rfl

@[simp]
/--
lemma `subcomplex_cast` / 引理 `subcomplex_cast`

English:
lemma subcomplex_cast
  given: (s : X.S) {d : Nat} (hd : s.dim = d)
  proof: by
  rw [cast_eq_self]

中文:
引理 subcomplex_cast
  条件: (s : X.S) {d : 自然数} (hd : s.dim = d)
  证明: by
  rw [cast_eq_self]

Depends on / 依赖: cast_eq_self
-/
lemma subcomplex_cast (s : X.S) {d : Nat} (hd : s.dim = d) :
    (s.cast hd).subcomplex = s.subcomplex := by
  rw [cast_eq_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder X.S
  body: Preorder.lift subcomplex

中文:
实例 :
  签名: Preorder X.S
  定义体: Preorder.lift subcomplex

Depends on / 依赖: Preorder, Preorder.lift, subcomplex
-/
instance : Preorder X.S := Preorder.lift subcomplex

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {s t : X.S}
  statement: s <= t ↔ s.subcomplex <= t.subcomplex
  proof: Iff.rfl

中文:
引理 le_def
  条件: {s t : X.S}
  结论: s <= t ↔ s.subcomplex <= t.subcomplex
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def {s t : X.S} : s <= t ↔ s.subcomplex <= t.subcomplex :=
  Iff.rfl

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {s t : X.S}
  proof: by
  rw [le_def]; rw [Subcomplex.ofSimplex_le_iff]; rw [Subfunctor.ofSection_obj]; rw [Set.mem_ofPred_eq]
  tauto

中文:
引理 le_iff
  条件: {s t : X.S}
  证明: by
  rw [le_def]; rw [Subcomplex.ofSimplex_le_iff]; rw [Subfunctor.ofSection_obj]; rw [Set.mem_ofPred_eq]
  tauto

Depends on / 依赖: Set.mem_ofPred_eq, Subcomplex, Subcomplex.ofSimplex_le_iff, Subfunctor, Subfunctor.ofSection_obj, le_def, mem_ofPred_eq, ofSection_obj, ofSimplex_le_iff
-/
lemma le_iff {s t : X.S} :
    s <= t ↔ exists (f : ⦋s.dim⦌ ⟶ ⦋t.dim⦌), X.map f.op t.simplex = s.simplex := by
  rw [le_def]; rw [Subcomplex.ofSimplex_le_iff]; rw [Subfunctor.ofSection_obj]; rw [Set.mem_ofPred_eq]
  tauto

/--
lemma `mk_map_le` / 引理 `mk_map_le`

English:
lemma mk_map_le
  given: {n m : Nat} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌)
  proof: by
  rw [le_iff]
  tauto

中文:
引理 mk_map_le
  条件: {n m : 自然数} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌)
  证明: by
  rw [le_iff]
  tauto

Depends on / 依赖: le_iff
-/
lemma mk_map_le {n m : Nat} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    S.mk (X.map f.op x) <= S.mk x := by
  rw [le_iff]
  tauto

/--
lemma `mk_map_eq_iff_of_mono` / 引理 `mk_map_eq_iff_of_mono`

English:
lemma mk_map_eq_iff_of_mono
  statement: {n m : Nat} (x : X _⦋n⦌)
  proof: by
  constructor
  · intro h
    obtain rfl := S.dim_eq_of_mk_eq h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    infer_instance
  · intro hf
    obtain rfl := SimplexCategory.eq_of_isIso f
    obtain rfl := SimplexCategory.eq_id_of_isIso f
    simp

中文:
引理 mk_map_eq_iff_of_mono
  结论: {n m : 自然数} (x : X _⦋n⦌)
  证明: by
  constructor
  · intro h
    obtain rfl := S.dim_eq_of_mk_eq h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    infer_instance
  · intro hf
    obtain rfl := SimplexCategory.eq_of_isIso f
    obtain rfl := SimplexCategory.eq_id_of_isIso f
    simp

Depends on / 依赖: S.dim_eq_of_mk_eq, SimplexCategory, SimplexCategory.eq_id_of_isIso, SimplexCategory.eq_id_of_mono, SimplexCategory.eq_of_isIso, dim_eq_of_mk_eq, eq_id_of_isIso, eq_id_of_mono, eq_of_isIso, infer_instance
-/
lemma mk_map_eq_iff_of_mono {n m : Nat} (x : X _⦋n⦌)
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] :
    S.mk (X.map f.op x) = S.mk x ↔ IsIso f := by
  constructor
  · intro h
    obtain rfl := S.dim_eq_of_mk_eq h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    infer_instance
  · intro hf
    obtain rfl := SimplexCategory.eq_of_isIso f
    obtain rfl := SimplexCategory.eq_id_of_isIso f
    simp

/-- The type of simplices of `X : SSet.{u}` identifies to the type
of elements of `X` considered as a functor `SimplexCategoryᵒᵖ ⥤ Type u`.
(Note that this is not an (anti)equivalence of categories,
see `S.le_iff_nonempty_hom`.) -/
@[simps!]
/--
Definition of `equivElements` / `equivElements` 的定义

English:
definition equivElements
  signature: : X.S ≃ X.Elements where
  body: X.elementsMk _ s.simplex
  invFun := by rintro ⟨⟨⟨n⟩⟩, x⟩; exact S.mk x
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivElements
  签名: : X.S ≃ X.Elements where
  定义体: X.elementsMk _ s.simplex
  invFun := by rintro ⟨⟨⟨n⟩⟩, x⟩; exact S.mk x
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: X.elementsMk, elementsMk, s.simplex, simplex
-/
def equivElements : X.S ≃ X.Elements where
  toFun s := X.elementsMk _ s.simplex
  invFun := by rintro ⟨⟨⟨n⟩⟩, x⟩; exact S.mk x
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `le_iff_nonempty_hom` / 引理 `le_iff_nonempty_hom`

English:
lemma le_iff_nonempty_hom
  given: (x y : X.S)
  proof: by
  rw [le_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f.op, hf⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, hf⟩

中文:
引理 le_iff_nonempty_hom
  条件: (x y : X.S)
  证明: by
  rw [le_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f.op, hf⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, hf⟩

Depends on / 依赖: f.op, f.unop, le_iff
-/
lemma le_iff_nonempty_hom (x y : X.S) :
    x <= y ↔ Nonempty (equivElements y ⟶ equivElements x) := by
  rw [le_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f.op, hf⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, hf⟩

/-- The bijection `X.op.S ≃ X.S`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : X.op.S ≃ X.S where
  body: S.mk (opObjEquiv x.simplex)
  invFun y := S.mk (opObjEquiv.symm y.simplex)

中文:
定义 opEquiv
  签名: : X.op.S ≃ X.S where
  定义体: S.mk (opObjEquiv x.simplex)
  invFun y := S.mk (opObjEquiv.symm y.simplex)

Depends on / 依赖: S.mk, opObjEquiv, simplex, x.simplex
-/
def opEquiv : X.op.S ≃ X.S where
  toFun x := S.mk (opObjEquiv x.simplex)
  invFun y := S.mk (opObjEquiv.symm y.simplex)

/-- The bijection `X.S ≃ Y.S` on simplices of simplicial sets that
is induced by an isomorphism `X ≅ Y`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `equivOfIso` / `equivOfIso` 的定义

English:
definition equivOfIso
  signature: {Y : SSet.{u}} (e : X ≅ Y)
  body: S.mk (e.hom.app _ s.simplex)
  invFun s := S.mk (e.inv.app _ s.simplex)
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 equivOfIso
  签名: {Y : SSet.{u}} (e : X ≅ Y)
  定义体: S.mk (e.hom.app _ s.simplex)
  invFun s := S.mk (e.inv.app _ s.simplex)
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: S.mk, e.hom.app, s.simplex, simplex
-/
def equivOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.S ≃ Y.S where
  toFun s := S.mk (e.hom.app _ s.simplex)
  invFun s := S.mk (e.inv.app _ s.simplex)
  left_inv _ := by simp
  right_inv _ := by simp

end S

end SSet
