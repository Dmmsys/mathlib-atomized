/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
# The partially ordered type of non degenerate simplices of a simplicial set

In this file, we introduce the partially ordered type `X.N` of
non degenerate simplices of a simplicial set `X`. We obtain
an embedding `X.orderEmbeddingN : X.N ↪o X.Subcomplex` which sends
a non degenerate simplex to the subcomplex of `X` it generates.

Given an arbitrary simplex `x : X.S`, we show that there is a unique
non degenerate `x.toN : X.N` such that `x.toN.subcomplex = x.subcomplex`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

/--
Definition of `N` / `N` 的定义

English:
structure N
  parameters: extends X.S
  extends: X.S
  (no additional axioms)

中文:
结构 N
  参数: extends X.S
  继承: X.S
  (无附加公理)
-/
structure N extends X.S where mk' ::
  nonDegenerate : simplex in X.nonDegenerate _

namespace N

variable {X}

/--
lemma `mk'_surjective` / 引理 `mk'_surjective`

English:
lemma mk'_surjective
  given: (s : X.N)
  proof: ⟨s.toS, s.nonDegenerate, rfl⟩

中文:
引理 mk'_surjective
  条件: (s : X.N)
  证明: ⟨s.toS, s.nonDegenerate, rfl⟩

Depends on / 依赖: nonDegenerate, s.nonDegenerate, s.toS
-/
lemma mk'_surjective (s : X.N) :
    exists (t : X.S) (ht : t.simplex in X.nonDegenerate _), s = mk' t ht :=
  ⟨s.toS, s.nonDegenerate, rfl⟩

/-- Constructor for the type of non degenerate simplices of a simplicial set. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  body: x
  nonDegenerate := hx

中文:
定义 mk
  签名: {n : 自然数} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  定义体: x
  nonDegenerate := hx
-/
def mk {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) : X.N where
  simplex := x
  nonDegenerate := hx

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (x : X.N)
  proof: ⟨x.dim, ⟨_, x.nonDegenerate⟩, rfl⟩

中文:
引理 mk_surjective
  条件: (x : X.N)
  证明: ⟨x.dim, ⟨_, x.nonDegenerate⟩, rfl⟩

Depends on / 依赖: nonDegenerate, x.dim, x.nonDegenerate
-/
lemma mk_surjective (x : X.N) :
    exists (n : Nat) (y : X.nonDegenerate n), x = N.mk _ y.prop :=
  ⟨x.dim, ⟨_, x.nonDegenerate⟩, rfl⟩

/-- Induction principle for the type `X.N` of nondegenerate simplices of
a simplicial set `X`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `induction` / `induction` 的定义

English:
definition induction
  signature: {motive : X.N -> Sort*}
  body: mk s.dim ⟨_, s.nonDegenerate⟩

@[simp]

中文:
定义 induction
  签名: {motive : X.N -> 类型层*}
  定义体: mk s.dim ⟨_, s.nonDegenerate⟩

@[simp]

Depends on / 依赖: nonDegenerate, s.dim, s.nonDegenerate
-/
def induction {motive : X.N -> Sort*}
    (mk : forall (n : Nat) (x : X.nonDegenerate n), motive (mk x.val x.property)) (s : X.N) :
    motive s :=
  mk s.dim ⟨_, s.nonDegenerate⟩

@[simp]
/--
lemma `induction_mk` / 引理 `induction_mk`

English:
lemma induction_mk
  statement: {motive : X.N -> Sort*}
  proof: rfl

中文:
引理 induction_mk
  结论: {motive : X.N -> 类型层*}
  证明: rfl

Depends on / 依赖: N.mk, motive, property, s.property, s.val
-/
lemma induction_mk {motive : X.N -> Sort*}
    (mk : forall (n : Nat) (x : X.nonDegenerate n), motive (mk x.1 x.2)) {n : Nat} (s : X.nonDegenerate n) :
  induction (motive := motive) mk (N.mk s.val s.property) = mk n s := rfl

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: (x y : X.N)
  proof: by
  grind [cases SSet.N]

中文:
引理 ext_iff
  条件: (x y : X.N)
  证明: by
  grind [cases SSet.N]

Depends on / 依赖: SSet.N
-/
lemma ext_iff (x y : X.N) :
    x = y ↔ x.toS = y.toS := by
  grind [cases SSet.N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder X.N
  body: Preorder.lift toS

中文:
实例 :
  签名: 预序 X.N
  定义体: Preorder.lift toS

Depends on / 依赖: Preorder, Preorder.lift
-/
instance : Preorder X.N := Preorder.lift toS

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {x y : X.N}
  statement: x <= y ↔ x.subcomplex <= y.subcomplex
  proof: Iff.rfl

中文:
引理 le_iff
  条件: {x y : X.N}
  结论: x <= y ↔ x.subcomplex <= y.subcomplex
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_iff {x y : X.N} : x <= y ↔ x.subcomplex <= y.subcomplex :=
  Iff.rfl

/--
lemma `lt_iff` / 引理 `lt_iff`

English:
lemma lt_iff
  given: {x y : X.N}
  statement: x < y ↔ x.subcomplex < y.subcomplex
  proof: Iff.rfl

中文:
引理 lt_iff
  条件: {x y : X.N}
  结论: x < y ↔ x.subcomplex < y.subcomplex
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lt_iff {x y : X.N} : x < y ↔ x.subcomplex < y.subcomplex :=
  Iff.rfl

/--
lemma `le_iff_exists_mono` / 引理 `le_iff_exists_mono`

English:
lemma le_iff_exists_mono
  given: {x y : X.N}
  proof: by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ => ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩

中文:
引理 le_iff_存在_mono
  条件: {x y : X.N}
  证明: by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ => ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Subfunctor.ofSection_le_iff, Subcomplex, Subcomplex.mem_ofSimplex_obj_iff, Subfunctor, X.mono_of_nonDegenerate, le_iff, mem_ofSimplex_obj_iff, mono_of_nonDegenerate, nonDegenerate, ofSection_le_iff, x.nonDegenerate
-/
lemma le_iff_exists_mono {x y : X.N} :
    x <= y ↔ exists (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex := by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ => ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩

/--
lemma `dim_le_of_le` / 引理 `dim_le_of_le`

English:
lemma dim_le_of_le
  given: {x y : X.N} (h : x <= y)
  statement: x.dim <= y.dim
  proof: by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

中文:
引理 dim_le_of_le
  条件: {x y : X.N} (h : x <= y)
  结论: x.dim <= y.dim
  证明: by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

Depends on / 依赖: SimplexCategory, SimplexCategory.len_le_of_mono, le_iff_exists_mono, len_le_of_mono
-/
lemma dim_le_of_le {x y : X.N} (h : x <= y) : x.dim <= y.dim := by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `dim_lt_of_lt` / 引理 `dim_lt_of_lt`

English:
lemma dim_lt_of_lt
  given: {x y : X.N} (h : x < y)
  statement: x.dim < y.dim
  proof: by
  obtain h' | h' := (dim_le_of_le h.le).lt_or_eq
  · exact h'
  · obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h.le
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obt

中文:
引理 dim_lt_of_lt
  条件: {x y : X.N} (h : x < y)
  结论: x.dim < y.dim
  证明: by
  obtain h' | h' := (dim_le_of_le h.le).lt_or_eq
  · exact h'
  · obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h.le
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obt

Depends on / 依赖: SimplexCategory, SimplexCategory.eq_id_of_mono, dim_le_of_le, eq_id_of_mono, h.le, le_iff_exists_mono, lt_or_eq, mk_surjective, x.mk_surjective, y.mk_surjective
-/
lemma dim_lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.dim := by
  obtain h' | h' := (dim_le_of_le h.le).lt_or_eq
  · exact h'
  · obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h.le
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obtain rfl : y = x := by simpa using hf
    simp at h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder X.N
  body: by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (dim_le_of_le h) (dim_le_of_le h')
    rw [le_iff_exists_mono] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aeso

中文:
实例 :
  签名: 偏序 X.N
  定义体: by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (dim_le_of_le h) (dim_le_of_le h')
    rw [le_iff_exists_mono] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aeso

Depends on / 依赖: SimplexCategory, SimplexCategory.eq_id_of_mono, dim_le_of_le, eq_id_of_mono, le_antisymm, le_iff_exists_mono, mk_surjective
-/
instance : PartialOrder X.N where
  le_antisymm x₁ x₂ h h' := by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (dim_le_of_le h) (dim_le_of_le h')
    rw [le_iff_exists_mono] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop

/--
lemma `subcomplex_injective` / 引理 `subcomplex_injective`

English:
lemma subcomplex_injective
  given: {x y : X.N} (h : x.subcomplex = y.subcomplex)
  proof: by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]

中文:
引理 subcomplex_injective
  条件: {x y : X.N} (h : x.subcomplex = y.subcomplex)
  证明: by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]

Depends on / 依赖: all_goals, le_antisymm, le_iff
-/
lemma subcomplex_injective {x y : X.N} (h : x.subcomplex = y.subcomplex) :
    x = y := by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]

/--
lemma `subcomplex_injective_iff` / 引理 `subcomplex_injective_iff`

English:
lemma subcomplex_injective_iff
  given: {x y : X.N}
  proof: ⟨subcomplex_injective, by rintro rfl; rfl⟩

中文:
引理 subcomplex_injective_iff
  条件: {x y : X.N}
  证明: ⟨subcomplex_injective, by rintro rfl; rfl⟩

Depends on / 依赖: subcomplex_injective
-/
lemma subcomplex_injective_iff {x y : X.N} :
    x.subcomplex = y.subcomplex ↔ x = y :=
  ⟨subcomplex_injective, by rintro rfl; rfl⟩

/--
lemma `eq_iff` / 引理 `eq_iff`

English:
lemma eq_iff
  given: {x y : X.N}
  proof: ⟨by rintro rfl; rfl, fun h => by simp [le_antisymm_iff, le_iff, h]⟩

中文:
引理 eq_iff
  条件: {x y : X.N}
  证明: ⟨by rintro rfl; rfl, fun h => by simp [le_antisymm_iff, le_iff, h]⟩

Depends on / 依赖: le_antisymm_iff, le_iff
-/
lemma eq_iff {x y : X.N} :
    x = y ↔ x.subcomplex = y.subcomplex :=
  ⟨by rintro rfl; rfl, fun h => by simp [le_antisymm_iff, le_iff, h]⟩

section

variable (s : X.N) {d : Nat} (hd : s.dim = d)

/--
Definition of `cast` / `cast` 的定义

English:
abbreviation cast
  signature: : X.N where
  body: s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate

中文:
缩写 cast
  签名: : X.N where
  定义体: s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate

Depends on / 依赖: s.toS.cast
-/
abbrev cast : X.N where
  toS := s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate

/--
lemma `cast_eq_self` / 引理 `cast_eq_self`

English:
lemma cast_eq_self
  statement: s.cast hd = s
  proof: by
  subst hd
  rfl

中文:
引理 cast_eq_self
  结论: s.cast hd = s
  证明: by
  subst hd
  rfl
-/
lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

variable (X) in
/--
lemma `iSup_subcomplex_eq_top` / 引理 `iSup_subcomplex_eq_top`

English:
lemma iSup_subcomplex_eq_top
  proof: le_antisymm (by simp) (by
    rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top X]; rw [iSup_le_iff]
    rintro ⟨d, s, hs⟩
    exact le_trans (by rfl) (le_iSup _ (N.mk _ hs)))

中文:
引理 iSup_subcomplex_eq_top
  证明: le_antisymm (by simp) (by
    rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top X]; rw [iSup_le_iff]
    rintro ⟨d, s, hs⟩
    exact le_trans (by rfl) (le_iSup _ (N.mk _ hs)))

Depends on / 依赖: N.mk, Subcomplex, Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top, iSup_le_iff, iSup_ofSimplex_nonDegenerate_eq_top, le_antisymm, le_iSup, le_trans
-/
lemma iSup_subcomplex_eq_top :
    ⨆ (s : X.N), s.subcomplex = ⊤ :=
  le_antisymm (by simp) (by
    rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top X]; rw [iSup_le_iff]
    rintro ⟨d, s, hs⟩
    exact le_trans (by rfl) (le_iSup _ (N.mk _ hs)))

/--
lemma `subcomplex_le_iff` / 引理 `subcomplex_le_iff`

English:
lemma subcomplex_le_iff
  given: {A B : X.Subcomplex}
  proof: by
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  refine ⟨fun h s => ?_, fun h n x hx => ?_⟩
  · induction s using N.induction with
    | mk n x =>
      intro hx
      simp only [Subfunctor.ofSection_le_iff, mk_simplex] at hx ⊢
      exact h _ _ hx
  · simpa using! h (N.mk _ x.prop) (by simpa)

中文:
引理 subcomplex_le_iff
  条件: {A B : X.子复形}
  证明: by
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  refine ⟨fun h s => ?_, fun h n x hx => ?_⟩
  · induction s using N.induction with
    | mk n x =>
      intro hx
      simp only [Subfunctor.ofSection_le_iff, mk_simplex] at hx ⊢
      exact h _ _ hx
  · simpa using! h (N.mk _ x.prop) (by simpa)

Depends on / 依赖: N.induction, N.mk, Subcomplex, Subcomplex.le_iff_contains_nonDegenerate, Subfunctor, Subfunctor.ofSection_le_iff, le_iff_contains_nonDegenerate, mk_simplex, ofSection_le_iff, x.prop
-/
lemma subcomplex_le_iff {A B : X.Subcomplex} :
    A <= B ↔ forall (s : X.N), s.subcomplex <= A -> s.subcomplex <= B := by
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  refine ⟨fun h s => ?_, fun h n x hx => ?_⟩
  · induction s using N.induction with
    | mk n x =>
      intro hx
      simp only [Subfunctor.ofSection_le_iff, mk_simplex] at hx ⊢
      exact h _ _ hx
  · simpa using! h (N.mk _ x.prop) (by simpa)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `X.op.N ≃ X.N`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : X.op.N ≃o X.N where
  body: N.mk (opObjEquiv x.simplex)
    (by simpa only [opObjEquiv_mem_nonDegenerate_iff] using x.nonDegenerate)
  invFun y := N.mk (opObjEquiv.symm y.simplex)
    (by simpa [← opObjEquiv_mem_nonDegenerate_iff] using y.nonDegenerate)
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofS

中文:
定义 opEquiv
  签名: : X.op.N ≃o X.N where
  定义体: N.mk (opObjEquiv x.simplex)
    (by simpa only [opObjEquiv_mem_nonDegenerate_iff] using x.nonDegenerate)
  invFun y := N.mk (opObjEquiv.symm y.simplex)
    (by simpa [← opObjEquiv_mem_nonDegenerate_iff] using y.nonDegenerate)
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofS

Depends on / 依赖: N.mk, opObjEquiv, simplex, x.simplex
-/
def opEquiv : X.op.N ≃o X.N where
  toFun x := N.mk (opObjEquiv x.simplex)
    (by simpa only [opObjEquiv_mem_nonDegenerate_iff] using x.nonDegenerate)
  invFun y := N.mk (opObjEquiv.symm y.simplex)
    (by simpa [← opObjEquiv_mem_nonDegenerate_iff] using y.nonDegenerate)
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofSimplex_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨SimplexCategory.rev.map f, by simp [op_map, dsimp% hf]⟩
    · rintro ⟨f, hf⟩
      exact ⟨SimplexCategory.rev.map f, by simp [op_map, ← hf]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `X.N ≃ Y.N` on nondegenerate simplices of simplicial sets
that is induced by an isomorphism `X ≅ Y`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `orderIsoOfIso` / `orderIsoOfIso` 的定义

English:
definition orderIsoOfIso
  signature: {Y : SSet.{u}} (e : X ≅ Y)
  body: N.mk (e.hom.app _ x.simplex)
    ((nonDegenerate_iff_of_isIso e.hom x.simplex).mpr x.nonDegenerate)
  invFun y := N.mk (e.inv.app _ y.simplex)
    ((nonDegenerate_iff_of_isIso e.inv y.simplex).mpr y.nonDegenerate)
  left_inv x := by simp [N.ext_iff, S.ext_iff']
  right_inv _ := by simp [N.ext_iff, S

中文:
定义 orderIsoOfIso
  签名: {Y : SSet.{u}} (e : X ≅ Y)
  定义体: N.mk (e.hom.app _ x.simplex)
    ((nonDegenerate_iff_of_isIso e.hom x.simplex).mpr x.nonDegenerate)
  invFun y := N.mk (e.inv.app _ y.simplex)
    ((nonDegenerate_iff_of_isIso e.inv y.simplex).mpr y.nonDegenerate)
  left_inv x := by simp [N.ext_iff, S.ext_iff']
  right_inv _ := by simp [N.ext_iff, S

Depends on / 依赖: N.mk, e.hom.app, simplex, x.simplex
-/
def orderIsoOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.N ≃o Y.N where
  toFun x := N.mk (e.hom.app _ x.simplex)
    ((nonDegenerate_iff_of_isIso e.hom x.simplex).mpr x.nonDegenerate)
  invFun y := N.mk (e.inv.app _ y.simplex)
    ((nonDegenerate_iff_of_isIso e.inv y.simplex).mpr y.nonDegenerate)
  left_inv x := by simp [N.ext_iff, S.ext_iff']
  right_inv _ := by simp [N.ext_iff, S.ext_iff']
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofSimplex_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    refine exists_congr (fun f => ?_)
    dsimp at f ⊢
    rw [← NatTrans.naturality_apply e.hom f.op]
    exact (e.app _).toEquiv.apply_eq_iff_eq

end N

/-- The map which sends a non degenerate simplex of a simplicial set to
the subcomplex it generates is an order embedding. -/
@[simps]
/--
Definition of `orderEmbeddingN` / `orderEmbeddingN` 的定义

English:
definition orderEmbeddingN
  signature: : X.N ↪o X.Subcomplex where
  body: x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

中文:
定义 orderEmbeddingN
  签名: : X.N ↪o X.子复形 where
  定义体: x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

Depends on / 依赖: subcomplex, x.subcomplex
-/
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

namespace S

variable {X}

/--
lemma `eq_iff_ofSimplex_eq` / 引理 `eq_iff_ofSimplex_eq`

English:
lemma eq_iff_ofSimplex_eq
  statement: {X : SSet.{u}} {n m : Nat} (x : X _⦋n⦌) (y : X _⦋m⦌)
  proof: by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl

中文:
引理 eq_iff_ofSimplex_eq
  结论: {X : SSet.{u}} {n m : 自然数} (x : X _⦋n⦌) (y : X _⦋m⦌)
  证明: by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl

Depends on / 依赖: N.ext_iff, N.mk, ext_iff, le_antisymm_iff
-/
lemma eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : Nat} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x in X.nonDegenerate _) (hy : y in X.nonDegenerate _) :
    S.mk x = S.mk y ↔ Subcomplex.ofSimplex x = Subcomplex.ofSimplex y := by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl

/--
lemma `subcomplex_map_le` / 引理 `subcomplex_map_le`

English:
lemma subcomplex_map_le
  statement: (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌)
  proof: by
  simp only [Subcomplex.ofSimplex_le_iff]
  exact ⟨_, hf⟩

中文:
引理 subcomplex_map_le
  结论: (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌)
  证明: by
  simp only [Subcomplex.ofSimplex_le_iff]
  exact ⟨_, hf⟩

Depends on / 依赖: Subcomplex, Subcomplex.ofSimplex_le_iff, ofSimplex_le_iff
-/
lemma subcomplex_map_le (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌)
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex <= y.subcomplex := by
  simp only [Subcomplex.ofSimplex_le_iff]
  exact ⟨_, hf⟩

/--
lemma `subcomplex_eq_of_epi` / 引理 `subcomplex_eq_of_epi`

English:
lemma subcomplex_eq_of_epi
  statement: (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
  proof: by
  refine le_antisymm (subcomplex_map_le x y f hf) ?_
  simp only [Subcomplex.ofSimplex_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← hf, ← Functor.map_comp_apply, ← op_comp]⟩

中文:
引理 subcomplex_eq_of_epi
  结论: (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [满态射 f]
  证明: by
  refine le_antisymm (subcomplex_map_le x y f hf) ?_
  simp only [Subcomplex.ofSimplex_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← hf, ← Functor.map_comp_apply, ← op_comp]⟩

Depends on / 依赖: Functor, Functor.map_comp_apply, Subcomplex, Subcomplex.ofSimplex_le_iff, isSplitEpi_of_epi, le_antisymm, map_comp_apply, ofSimplex_le_iff, op_comp, section_, subcomplex_map_le
-/
lemma subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex = y.subcomplex := by
  refine le_antisymm (subcomplex_map_le x y f hf) ?_
  simp only [Subcomplex.ofSimplex_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← hf, ← Functor.map_comp_apply, ← op_comp]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `existsUnique_n` / 引理 `existsUnique_n`

English:
lemma existsUnique_n
  given: (x : X.S)
  statement: exists! (y : X.N), y.subcomplex = x.subcomplex
  proof: existsUnique_of_exists_of_unique (by
    obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
    obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
    refine ⟨N.mk _ y.prop, le_antisymm ?_ ?_⟩
    · simp only [Subcomplex.ofSimplex_le_iff]
      have := isSplitEpi_of_epi f
      have : Function.Injective (X

中文:
引理 存在Unique_n
  条件: (x : X.S)
  结论: 存在! (y : X.N), y.subcomplex = x.subcomplex
  证明: existsUnique_of_exists_of_unique (by
    obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
    obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
    refine ⟨N.mk _ y.prop, le_antisymm ?_ ?_⟩
    · simp only [Subcomplex.ofSimplex_le_iff]
      have := isSplitEpi_of_epi f
      have : Function.Injective (X

Depends on / 依赖: Catego, Function, Function.Injective, Functor, Functor.map_comp, Injective, N.mk, Subcomplex, Subcomplex.ofSimplex_le_iff, X.exists_nonDegenerate, X.map, comp_apply, existsUnique_of_exists_of_unique, exists_nonDegenerate, f.op, infer_instance, isSplitEpi_of_epi, le_antisymm, map_comp, mk_surjective
-/
lemma existsUnique_n (x : X.S) : exists! (y : X.N), y.subcomplex = x.subcomplex :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
    obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
    refine ⟨N.mk _ y.prop, le_antisymm ?_ ?_⟩
    · simp only [Subcomplex.ofSimplex_le_iff]
      have := isSplitEpi_of_epi f
      have : Function.Injective (X.map f.op) := by
        rw [← mono_iff_injective]
        infer_instance
      refine ⟨(section_ f).op, this ?_⟩
      dsimp
      rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]; rw [Category.assoc]; rw [IsSplitEpi.id]; rw [Category.comp_id]
    · simp only [Subcomplex.ofSimplex_le_iff]
      exact ⟨f.op, rfl⟩)
    (fun y₁ y₂ h₁ h₂ => N.subcomplex_injective (by rw [h₁, h₂]))

/--
Definition of `toN` / `toN` 的定义

English:
definition toN
  signature: (x : X.S)
  body: x.existsUnique_n.exists.choose

@[simp]

中文:
定义 toN
  签名: (x : X.S)
  定义体: x.existsUnique_n.exists.choose

@[simp]

Depends on / 依赖: existsUnique_n, x.existsUnique_n.exists.choose
-/
noncomputable def toN (x : X.S) : X.N := x.existsUnique_n.exists.choose

@[simp]
/--
lemma `subcomplex_toN` / 引理 `subcomplex_toN`

English:
lemma subcomplex_toN
  given: (x : X.S)
  statement: x.toN.subcomplex = x.subcomplex
  proof: x.existsUnique_n.exists.choose_spec

中文:
引理 subcomplex_toN
  条件: (x : X.S)
  结论: x.toN.subcomplex = x.subcomplex
  证明: x.existsUnique_n.exists.choose_spec

Depends on / 依赖: choose_spec, existsUnique_n, x.existsUnique_n.exists.choose_spec
-/
lemma subcomplex_toN (x : X.S) : x.toN.subcomplex = x.subcomplex :=
  x.existsUnique_n.exists.choose_spec

/--
lemma `toN_eq_iff` / 引理 `toN_eq_iff`

English:
lemma toN_eq_iff
  given: {x : X.S} {y : X.N}
  proof: ⟨by rintro rfl; simp, fun h => x.existsUnique_n.unique (by simp) h⟩

中文:
引理 toN_eq_iff
  条件: {x : X.S} {y : X.N}
  证明: ⟨by rintro rfl; simp, fun h => x.existsUnique_n.unique (by simp) h⟩

Depends on / 依赖: existsUnique_n, unique, x.existsUnique_n.unique
-/
lemma toN_eq_iff {x : X.S} {y : X.N} :
    x.toN = y ↔ y.subcomplex = x.subcomplex :=
  ⟨by rintro rfl; simp, fun h => x.existsUnique_n.unique (by simp) h⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `existsUnique_toNπ` / 引理 `existsUnique_toNπ`

English:
lemma existsUnique_toNπ
  given: {x : X.S} {y : X.N} (hy : x.toN = y)
  proof: by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff]; rw [hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  refine existsUnique_of_exists_of_unique ⟨f, in

中文:
引理 存在Unique_toNπ
  条件: {x : X.S} {y : X.N} (hy : x.toN = y)
  证明: by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff]; rw [hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  refine existsUnique_of_exists_of_unique ⟨f, in

Depends on / 依赖: N.mk, N.subcomplex_injective_iff, X.exists_nonDegenerate, existsUnique_of_exists_of_unique, exists_nonDegenerate, mk_surjective, subcomplex_eq_of_epi, subcomplex_injective_iff, toN_eq_iff, unique_nonDegenerate_map, x.mk_surjective
-/
lemma existsUnique_toNπ {x : X.S} {y : X.N} (hy : x.toN = y) :
    exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Epi f ∧ X.map f.op y.simplex = x.simplex := by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff]; rw [hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  refine existsUnique_of_exists_of_unique ⟨f, inferInstance, rfl⟩
    (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ => unique_nonDegenerate_map _ _ _ _ hf₁.symm _ _ hf₂.symm)

/--
Definition of `toNπ` / `toNπ` 的定义

English:
definition toNπ
  signature: (x : X.S)
  body: (existsUnique_toNπ rfl).exists.choose

中文:
定义 toNπ
  签名: (x : X.S)
  定义体: (existsUnique_toNπ rfl).exists.choose
-/
@[no_expose] noncomputable def toNπ (x : X.S) : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌ :=
  (existsUnique_toNπ rfl).exists.choose

instance (x : X.S) : Epi x.toNπ := (existsUnique_toNπ rfl).exists.choose_spec.1

@[simp]
/--
lemma `map_toNπ_op_apply` / 引理 `map_toNπ_op_apply`

English:
lemma map_toNπ_op_apply
  given: (x : X.S)
  proof: (existsUnique_toNπ rfl).exists.choose_spec.2

中文:
引理 map_toNπ_op_apply
  条件: (x : X.S)
  证明: (existsUnique_toNπ rfl).exists.choose_spec.2

Depends on / 依赖: choose_spec, exists.choose_spec
-/
lemma map_toNπ_op_apply (x : X.S) :
    X.map x.toNπ.op x.toN.simplex = x.simplex := (existsUnique_toNπ rfl).exists.choose_spec.2

/--
lemma `dim_toN_le` / 引理 `dim_toN_le`

English:
lemma dim_toN_le
  given: (x : X.S)
  proof: SimplexCategory.le_of_epi x.toNπ

中文:
引理 dim_toN_le
  条件: (x : X.S)
  证明: SimplexCategory.le_of_epi x.toNπ

Depends on / 依赖: SimplexCategory, SimplexCategory.le_of_epi, le_of_epi, x.toN
-/
lemma dim_toN_le (x : X.S) :
    x.toN.dim <= x.dim :=
  SimplexCategory.le_of_epi x.toNπ

end S

end SSet
