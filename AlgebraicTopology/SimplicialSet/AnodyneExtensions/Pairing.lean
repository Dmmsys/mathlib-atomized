/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.IsUniquelyCodimOneFace

/-!
# Pairings

In this file, we introduce the definition of a pairing for a subcomplex `A`
of a simplicial set `X`, following the ideas by Sean Moss,
*Another approach to the Kan-Quillen model structure*, who gave a
complete combinatorial characterization of strong (inner) anodyne extensions.
Strong (inner) anodyne extensions are transfinite compositions of pushouts of coproducts
of (inner) horn inclusions, i.e. this is similar to (inner) anodyne extensions but
without the stability property under retracts.

A pairing for `A` consists in the data of a partition of the nondegenerate
simplices of `X` not in `A` into type (I) simplices and type (II) simplices,
and of a bijection between the types of type (I) and type (II) simplices.
Indeed, the main observation is that when we attach a simplex along a horn
inclusion, exactly two nondegenerate simplices are added: this simplex,
and the unique face which is not in the image of the horn. The former shall be
considered as of type (I) and the latter as type (II).

We say that a pairing is *regular* (typeclass `Pairing.IsRegular`) when
- it is proper (`Pairing.IsProper`), i.e. any type (II) simplex is uniquely
  a face of the corresponding type (I) simplex.
- a certain ancestrality relation is well founded.

When these conditions are satisfied, the inclusion `A.ι : A ⟶ X` is
a strong anodyne extension (TODO @joelriou), and the converse is also true
(if `A.ι` is a strong anodyne extension, then there is a regular pairing for `A` (TODO)).

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/--
Definition of `Pairing` / `Pairing` 的定义

English:
structure Pairing
  parameters: where
  axioms and operations (5):
    - I : Set A.N
    - II : Set A.N
    - inter : I inter II = ∅
    - union : I union II = Set.univ
    - p : II ≃ I

中文:
结构 Pairing
  参数: where
  公理与运算 (5 个):
    - I : 集合 A.N
    - II : 集合 A.N
    - inter : I inter II = ∅
    - union : I union II = 集合.univ
    - p : II ≃ I
-/
structure Pairing where
  /-- the set of type (I) simplices -/
  I : Set A.N
  /-- the set of type (II) simplices -/
  II : Set A.N
  inter : I inter II = ∅
  union : I union II = Set.univ
  /-- a bijection from the type (II) simplices to the type (I) simplices -/
  p : II ≃ I

namespace Pairing

variable {A} (P : A.Pairing)

/--
Definition of `IsProper` / `IsProper` 的定义

English:
class IsProper
  parameters: where
  axioms and operations (1):
    - isUniquelyCodimOneFace((x : P.II)) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS

中文:
类 是真
  参数: where
  公理与运算 (1 个):
    - isUniquelyCodimOneFace((x : P.II)) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
-/
class IsProper where
  isUniquelyCodimOneFace (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS

/--
lemma `isUniquelyCodimOneFace` / 引理 `isUniquelyCodimOneFace`

English:
lemma isUniquelyCodimOneFace
  given: [P.IsProper] (x : P.II)
  proof: IsProper.isUniquelyCodimOneFace x

@[simp]

中文:
引理 isUniquelyCodimOneFace
  条件: [P.是真] (x : P.II)
  证明: IsProper.isUniquelyCodimOneFace x

@[simp]

Depends on / 依赖: IsProper, IsProper.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS :=
  IsProper.isUniquelyCodimOneFace x

@[simp]
/--
lemma `dim_p` / 引理 `dim_p`

English:
lemma dim_p
  given: [P.IsProper] (x : P.II)
  proof: (P.isUniquelyCodimOneFace x).dim_eq

中文:
引理 dim_p
  条件: [P.是真] (x : P.II)
  证明: (P.isUniquelyCodimOneFace x).dim_eq

Depends on / 依赖: P.isUniquelyCodimOneFace, dim_eq, isUniquelyCodimOneFace
-/
lemma dim_p [P.IsProper] (x : P.II) :
    (P.p x).1.dim = x.1.dim + 1 :=
  (P.isUniquelyCodimOneFace x).dim_eq

/--
Definition of `IsInner` / `IsInner` 的定义

English:
class IsInner
  parameters: [P.IsProper]
  axioms and operations (2):
    - ne_zero((x : P.II) {d : Nat} (hd : x.1.dim = d)) : (P.isUniquelyCodimOneFace x).index hd != 0
    - ne_last((x : P.II) {d : Nat} (hd : x.1.dim = d)) : (P.isUniquelyCodimOneFace x).index hd != Fin.last _

中文:
类 是内积
  参数: [P.是真]
  公理与运算 (2 个):
    - ne_zero((x : P.II) {d : 自然数} (hd : x.1.dim = d)) : (P.isUniquelyCodimOneFace x).index hd != 0
    - ne_last((x : P.II) {d : 自然数} (hd : x.1.dim = d)) : (P.isUniquelyCodimOneFace x).index hd != 有限集.last _
-/
class IsInner [P.IsProper] : Prop where
  ne_zero (x : P.II) {d : Nat} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd != 0
  ne_last (x : P.II) {d : Nat} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd != Fin.last _

/--
Definition of `AncestralRel` / `AncestralRel` 的定义

English:
definition AncestralRel
  signature: (x y : P.II)
  body: x != y ∧ x.1 < (P.p y).1

中文:
定义 AncestralRel
  签名: (x y : P.II)
  定义体: x != y ∧ x.1 < (P.p y).1
-/
def AncestralRel (x y : P.II) : Prop :=
  x != y ∧ x.1 < (P.p y).1

variable {P} in
/--
lemma `AncestralRel.dim_le` / 引理 `AncestralRel.dim_le`

English:
lemma AncestralRel.dim_le
  given: [P.IsProper] {x y : P.II} (hxy : P.AncestralRel x y)
  proof: by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using
    SSet.N.dim_lt_of_lt hxy.2

中文:
引理 AncestralRel.dim_le
  条件: [P.是真] {x y : P.II} (hxy : P.AncestralRel x y)
  证明: by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using
    SSet.N.dim_lt_of_lt hxy.2

Depends on / 依赖: Nat.lt_succ_iff, P.isUniquelyCodimOneFace, SSet.N.dim_lt_of_lt, dim_eq, dim_lt_of_lt, isUniquelyCodimOneFace, lt_succ_iff
-/
lemma AncestralRel.dim_le [P.IsProper] {x y : P.II} (hxy : P.AncestralRel x y) :
    x.1.dim <= y.1.dim := by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using
    SSet.N.dim_lt_of_lt hxy.2

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
class IsRegular
  parameters: extends P.IsProper
  extends: P.IsProper
  axioms and operations (1):
    - wf : WellFounded P.AncestralRel

中文:
类 是正则
  参数: extends P.是真
  继承: P.是真
  公理与运算 (1 个):
    - wf : 良基 P.AncestralRel
-/
class IsRegular extends P.IsProper where
  wf : WellFounded P.AncestralRel

section

variable [P.IsRegular]

/--
lemma `wf` / 引理 `wf`

English:
lemma wf
  statement: WellFounded P.AncestralRel
  proof: IsRegular.wf

中文:
引理 wf
  结论: 良基 P.AncestralRel
  证明: IsRegular.wf

Depends on / 依赖: IsRegular, IsRegular.wf
-/
lemma wf : WellFounded P.AncestralRel := IsRegular.wf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsWellFounded _ P.AncestralRel
  body: P.wf

中文:
实例 :
  签名: 是良基 _ P.AncestralRel
  定义体: P.wf

Depends on / 依赖: P.wf
-/
instance : IsWellFounded _ P.AncestralRel where
  wf := P.wf

end

/--
lemma `exists_or` / 引理 `exists_or`

English:
lemma exists_or
  given: (x : A.N)
  proof: by
  have := Set.mem_univ x
  rw [← P.union]; rw [Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩

中文:
引理 存在_or
  条件: (x : A.N)
  证明: by
  have := Set.mem_univ x
  rw [← P.union]; rw [Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩

Depends on / 依赖: Or.inl, Or.inr, P.p.surjective, P.union, Set.mem_union, Set.mem_univ, mem_union, mem_univ, surjective
-/
lemma exists_or (x : A.N) :
    exists (y : P.II), x = y ∨ x = P.p y := by
  have := Set.mem_univ x
  rw [← P.union]; rw [Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩

/--
lemma `ne` / 引理 `ne`

English:
lemma ne
  given: (x : P.I) (y : P.II)
  proof: by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rintro rfl
  have : x in P.I inter P.II := ⟨hx, hy⟩
  simp [P.inter] at this

中文:
引理 ne
  条件: (x : P.I) (y : P.II)
  证明: by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rintro rfl
  have : x in P.I inter P.II := ⟨hx, hy⟩
  simp [P.inter] at this

Depends on / 依赖: P.II, P.inter
-/
lemma ne (x : P.I) (y : P.II) :
    x.1 != y.1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rintro rfl
  have : x in P.I inter P.II := ⟨hx, hy⟩
  simp [P.inter] at this

/--
lemma `le` / 引理 `le`

English:
lemma le
  given: [P.IsProper] (x : P.II)
  proof: (P.isUniquelyCodimOneFace x).le

中文:
引理 le
  条件: [P.是真] (x : P.II)
  证明: (P.isUniquelyCodimOneFace x).le

Depends on / 依赖: P.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
lemma le [P.IsProper] (x : P.II) :
    x.1 <= (P.p x).1 :=
  (P.isUniquelyCodimOneFace x).le

/--
lemma `lt` / 引理 `lt`

English:
lemma lt
  given: [P.IsProper] (x : P.II)
  proof: lt_of_le_of_ne' (P.le x) (P.ne _ _)

中文:
引理 lt
  条件: [P.是真] (x : P.II)
  证明: lt_of_le_of_ne' (P.le x) (P.ne _ _)

Depends on / 依赖: P.le, P.ne, lt_of_le_of_ne
-/
lemma lt [P.IsProper] (x : P.II) :
    x.1 < (P.p x).1 :=
  lt_of_le_of_ne' (P.le x) (P.ne _ _)

variable {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B)

/-- Given an isomorphism `Y ≅ X` of simplicial sets, a pairing `P` of a subcomplex
`A` of `X`, this is a pairing for a subcomplex `B` of `Y` if `A.preimage e.hom = B`. -/
@[simps I II]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: : B.Pairing where
  body: Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.I
  II := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := ((Subcomplex.N.orderIsoOfIso e hA).subtypeEquiv (by simp)).trans
    (P.p.trans ((Subcomplex.N.orderIs

中文:
定义 ofIso
  签名: : B.Pairing where
  定义体: Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.I
  II := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := ((Subcomplex.N.orderIsoOfIso e hA).subtypeEquiv (by simp)).trans
    (P.p.trans ((Subcomplex.N.orderIs

Depends on / 依赖: Subcomplex, Subcomplex.N.orderIsoOfIso, orderIsoOfIso
-/
def ofIso : B.Pairing where
  I := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.I
  II := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := ((Subcomplex.N.orderIsoOfIso e hA).subtypeEquiv (by simp)).trans
    (P.p.trans ((Subcomplex.N.orderIsoOfIso e hA).symm.subtypeEquiv (by simp)))

/-- A unification hint for the type (I) simplices of `Pairing.ofIso`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
    {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B) where
  ⊢ (P.ofIso e hA).I ≟ (N.orderIsoOfIso e hA) ⁻¹' P.I

/-- A unification hint for the type (II) simplices of `Pairing.ofIso`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
    {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B) where
  ⊢ (P.ofIso e hA).II ≟ (N.orderIsoOfIso e hA) ⁻¹' P.II

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `ofIso_p` / 引理 `ofIso_p`

English:
lemma ofIso_p
  given: (x : P.II)
  proof: by
  let e' := Subcomplex.N.orderIsoOfIso e hA
  ext
  change e'.symm (P.p ⟨e' (e'.symm x), _⟩) = e'.symm (P.p x)
  simp

中文:
引理 ofIso_p
  条件: (x : P.II)
  证明: by
  let e' := Subcomplex.N.orderIsoOfIso e hA
  ext
  change e'.symm (P.p ⟨e' (e'.symm x), _⟩) = e'.symm (P.p x)
  simp

Depends on / 依赖: Subcomplex, Subcomplex.N.orderIsoOfIso, orderIsoOfIso
-/
lemma ofIso_p (x : P.II) :
    dsimp% (P.ofIso e hA).p ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩ =
    ⟨(Subcomplex.N.orderIsoOfIso e hA).symm (P.p x), by simp⟩ := by
  let e' := Subcomplex.N.orderIsoOfIso e hA
  ext
  change e'.symm (P.p ⟨e' (e'.symm x), _⟩) = e'.symm (P.p x)
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `ofIso_ancestralRel_iff` / 引理 `ofIso_ancestralRel_iff`

English:
lemma ofIso_ancestralRel_iff
  given: (x y : P.II)
  proof: and_congr (not_congr (by aesop)) (by simp)

中文:
引理 ofIso_ancestralRel_iff
  条件: (x y : P.II)
  证明: and_congr (not_congr (by aesop)) (by simp)

Depends on / 依赖: and_congr, not_congr
-/
lemma ofIso_ancestralRel_iff (x y : P.II) :
    (P.ofIso e hA).AncestralRel
      ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩
      ⟨(Subcomplex.N.orderIsoOfIso e hA).symm y, by simp⟩ ↔
    P.AncestralRel x y :=
  and_congr (not_congr (by aesop)) (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsProper]
  signature: : (P.ofIso e hA).IsProper where
  body: by
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective x
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hx
    simp only [ofIso_II, ofIso_I, dsimp% P.ofIso_p e hA ⟨x, hx⟩]
    exact (P.isUniquelyCodimOneFace ⟨x, hx⟩).of_iso e.symm

中文:
实例 [P.是真]
  签名: : (P.ofIso e hA).是真 where
  定义体: by
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective x
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hx
    simp only [ofIso_II, ofIso_I, dsimp% P.ofIso_p e hA ⟨x, hx⟩]
    exact (P.isUniquelyCodimOneFace ⟨x, hx⟩).of_iso e.symm

Depends on / 依赖: N.orderIsoOfIso, OrderIso, OrderIso.apply_symm_apply, P.isUniquelyCodimOneFace, P.ofIso_p, Set.mem_preimage, apply_symm_apply, e.symm, isUniquelyCodimOneFace, mem_preimage, ofIso_I, ofIso_II, ofIso_p, of_iso, orderIsoOfIso, surjective, symm.surjective
-/
instance [P.IsProper] : (P.ofIso e hA).IsProper where
  isUniquelyCodimOneFace := by
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective x
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hx
    simp only [ofIso_II, ofIso_I, dsimp% P.ofIso_p e hA ⟨x, hx⟩]
    exact (P.isUniquelyCodimOneFace ⟨x, hx⟩).of_iso e.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsRegular]
  signature: : (P.ofIso e hA).IsRegular where
  body: by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.ofIso_ancestralRel_iff e hA] using hf n

中文:
实例 [P.是正则]
  签名: : (P.ofIso e hA).是正则 where
  定义体: by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.ofIso_ancestralRel_iff e hA] using hf n

Depends on / 依赖: P.ofIso_ancestralRel_iff, P.wf, hP.false, ofIso_ancestralRel_iff, wellFounded_iff_isEmpty_descending_chain
-/
instance [P.IsRegular] : (P.ofIso e hA).IsRegular where
  wf := by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.ofIso_ancestralRel_iff e hA] using hf n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ofIso_index` / 引理 `ofIso_index`

English:
lemma ofIso_index
  given: (x : P.II) {d : Nat} (hd : x.1.dim = d) [P.IsProper]
  proof: by
  rw [← (P.isUniquelyCodimOneFace x).index_of_iso e.symm hd]
  congr
  rw [P.ofIso_p e hA x]
  rfl

中文:
引理 ofIso_index
  条件: (x : P.II) {d : 自然数} (hd : x.1.dim = d) [P.是真]
  证明: by
  rw [← (P.isUniquelyCodimOneFace x).index_of_iso e.symm hd]
  congr
  rw [P.ofIso_p e hA x]
  rfl

Depends on / 依赖: P.isUniquelyCodimOneFace, P.ofIso_p, e.symm, index_of_iso, isUniquelyCodimOneFace, ofIso_p
-/
lemma ofIso_index (x : P.II) {d : Nat} (hd : x.1.dim = d) [P.IsProper] :
    ((P.ofIso e hA).isUniquelyCodimOneFace ⟨(N.orderIsoOfIso e hA).symm x, by simp⟩).index hd =
      (isUniquelyCodimOneFace P x).index hd := by
  rw [← (P.isUniquelyCodimOneFace x).index_of_iso e.symm hd]
  congr
  rw [P.ofIso_p e hA x]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsProper]
  signature: [P.IsInner]
  body: by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_zero ⟨a, hb⟩ hd
  ne_last := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a

中文:
实例 [P.是真]
  签名: [P.是内积]
  定义体: by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_zero ⟨a, hb⟩ hd
  ne_last := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a

Depends on / 依赖: IsInner, IsInner.ne_last, IsInner.ne_zero, N.orderIsoOfIso, OrderIso, OrderIso.apply_symm_apply, P.ofIso_index, Set.mem_preimage, apply_symm_apply, mem_preimage, ne_last, ne_zero, ofIso_II, ofIso_index, orderIsoOfIso, surjective, symm.surjective
-/
instance [P.IsProper] [P.IsInner] : (P.ofIso e hA).IsInner where
  ne_zero := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_zero ⟨a, hb⟩ hd
  ne_last := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_last ⟨a, hb⟩ hd

end Pairing

end SSet.Subcomplex
