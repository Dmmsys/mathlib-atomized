/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
# The type of nondegenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/--
Definition of `N` / `N` 的定义

English:
structure N
  parameters: extends X.N
  extends: X.N
  (no additional axioms)

中文:
结构 N
  参数: extends X.N
  继承: X.N
  (无附加公理)
-/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

/--
lemma `mk'_surjective` / 引理 `mk'_surjective`

English:
lemma mk'_surjective
  given: (s : A.N)
  proof: ⟨s.toN, s.notMem, rfl⟩

中文:
引理 mk'_surjective
  条件: (s : A.N)
  证明: ⟨s.toN, s.notMem, rfl⟩

Depends on / 依赖: notMem, s.notMem, s.toN
-/
lemma mk'_surjective (s : A.N) :
    exists (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩

/-- Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set. -/
@[simps!]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  body: x
  nonDegenerate := hx
  notMem := hx'

中文:
定义 mk
  签名: {n : 自然数} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  定义体: x
  nonDegenerate := hx
  notMem := hx'
-/
def mk {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
    (hx' : x ∉ A.obj _) : A.N where
  simplex := x
  nonDegenerate := hx
  notMem := hx'

/-- A unification hint for the dimension of `Subcomplex.N.mk`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (n : Nat) (x : X _⦋n⦌)
    (hx : x in X.nonDegenerate n) (hx' : x ∉ A.obj _) where
  ⊢ (mk x hx hx').dim ≟ n

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (s : A.N)
  proof: ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

中文:
引理 mk_surjective
  条件: (s : A.N)
  证明: ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

Depends on / 依赖: nonDegenerate, notMem, s.dim, s.nonDegenerate, s.notMem, s.simplex, simplex
-/
lemma mk_surjective (s : A.N) :
    exists (n : Nat) (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
      (hx' : x ∉ A.obj _), s = mk x hx hx' :=
  ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: (x y : A.N)
  proof: by
  grind [cases SSet.Subcomplex.N]

中文:
引理 ext_iff
  条件: (x y : A.N)
  证明: by
  grind [cases SSet.Subcomplex.N]

Depends on / 依赖: SSet.Subcomplex.N, Subcomplex
-/
lemma ext_iff (x y : A.N) :
    x = y ↔ x.toN = y.toN := by
  grind [cases SSet.Subcomplex.N]

variable (A) in
@[elab_as_elim]
/--
lemma `cases` / 引理 `cases`

English:
lemma cases
  statement: {motive : X.N -> Prop}
  proof: by
  by_cases hs : s.subcomplex <= A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))

中文:
引理 cases
  结论: {motive : X.N -> 命题}
  证明: by
  by_cases hs : s.subcomplex <= A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))

Depends on / 依赖: notMem, s.subcomplex, subcomplex
-/
lemma cases {motive : X.N -> Prop}
    (mem : forall (s : X.N), s.subcomplex <= A -> motive s)
    (notMem : forall (s : A.N), motive s.toN)
    (s : X.N) :
    motive s := by
  by_cases hs : s.subcomplex <= A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))

/--
lemma `eq_iff_sMk_eq` / 引理 `eq_iff_sMk_eq`

English:
lemma eq_iff_sMk_eq
  given: {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N)
  proof: by
  rw [N.ext_iff]; rw [SSet.N.ext_iff]

中文:
引理 eq_iff_sMk_eq
  条件: {X : SSet.{u}} {A : X.子复形} (x y : A.N)
  证明: by
  rw [N.ext_iff]; rw [SSet.N.ext_iff]

Depends on / 依赖: N.ext_iff, SSet.N.ext_iff, ext_iff
-/
lemma eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) :
    x = y ↔ S.mk x.simplex = S.mk y.simplex := by
  rw [N.ext_iff]; rw [SSet.N.ext_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder A.N
  body: PartialOrder.lift toN (fun _ _ => by simp [ext_iff])

中文:
实例 :
  签名: 偏序 A.N
  定义体: PartialOrder.lift toN (fun _ _ => by simp [ext_iff])

Depends on / 依赖: PartialOrder, PartialOrder.lift, ext_iff
-/
instance : PartialOrder A.N :=
  PartialOrder.lift toN (fun _ _ => by simp [ext_iff])

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {x y : A.N}
  statement: x <= y ↔ x.toN <= y.toN
  proof: Iff.rfl

中文:
引理 le_iff
  条件: {x y : A.N}
  结论: x <= y ↔ x.toN <= y.toN
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_iff {x y : A.N} : x <= y ↔ x.toN <= y.toN :=
  Iff.rfl

/--
lemma `lt_iff` / 引理 `lt_iff`

English:
lemma lt_iff
  given: {x y : A.N}
  statement: x < y ↔ x.toN < y.toN
  proof: Iff.rfl

中文:
引理 lt_iff
  条件: {x y : A.N}
  结论: x < y ↔ x.toN < y.toN
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN :=
  Iff.rfl

section

variable (s : A.N) {d : Nat} (hd : s.dim = d)

/--
Definition of `cast` / `cast` 的定义

English:
abbreviation cast
  signature: : A.N where
  body: s.toN.cast hd
  notMem := hd ▸ s.notMem

中文:
缩写 cast
  签名: : A.N where
  定义体: s.toN.cast hd
  notMem := hd ▸ s.notMem

Depends on / 依赖: s.toN.cast
-/
abbrev cast : A.N where
  toN := s.toN.cast hd
  notMem := hd ▸ s.notMem

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

/-- A unification hint for the dimension of `Subcomplex.N.cast`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (s : A.N) (d : Nat)
    (hd : s.dim = d) where
  ⊢ (s.cast hd).dim ≟ d

/-- The bijection `A.op.N ≃ A.N` for a subcomplex `A` of a simplicial set.. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : A.op.N ≃o A.N where
  body: N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

中文:
定义 opEquiv
  签名: : A.op.N ≃o A.N where
  定义体: N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

Depends on / 依赖: N.mk, SSet.N.opEquiv, notMem, opEquiv, x.notMem, x.toN
-/
def opEquiv : A.op.N ≃o A.N where
  toFun x := N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

/-- The bijection `A.N ≃ B.N` on nondegenerate simplices not belonging
to a certain subcomplex that is induced by an isomorphism `X ≅ Y` of
simplicial sets which maps `A : X.Subcomplex` to `B : Y.Subcomplex`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `orderIsoOfIso` / `orderIsoOfIso` 的定义

English:
definition orderIsoOfIso
  signature: {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y)
  body: N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).m

中文:
定义 orderIsoOfIso
  签名: {Y : SSet.{u}} {B : Y.子复形} (e : X ≅ Y)
  定义体: N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).m

Depends on / 依赖: N.mk, SSet.N.orderIsoOfIso, notMem, orderIsoOfIso, x.notMem, x.toN
-/
def orderIsoOfIso {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y)
    (hA : B.preimage e.hom = A) : A.N ≃o B.N where
  toFun x := N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).map_rel_iff'

end N

/--
lemma `existsN` / 引理 `existsN`

English:
lemma existsN
  statement: {X : SSet.{u}} {n : Nat} (s : X _⦋n⦌) {A : X.Subcomplex}
  proof: by
  refine ⟨⟨(S.mk s).toN, fun h => hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

中文:
引理 存在N
  结论: {X : SSet.{u}} {n : 自然数} (s : X _⦋n⦌) {A : X.子复形}
  证明: by
  refine ⟨⟨(S.mk s).toN, fun h => hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

Depends on / 依赖: S.map_toN, S.mk, ofSimplex_le_iff
-/
lemma existsN {X : SSet.{u}} {n : Nat} (s : X _⦋n⦌) {A : X.Subcomplex}
    (hs : s ∉ A.obj _) :
    exists (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex = s := by
  refine ⟨⟨(S.mk s).toN, fun h => hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

end SSet.Subcomplex
