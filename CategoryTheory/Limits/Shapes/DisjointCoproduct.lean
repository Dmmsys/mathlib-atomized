/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# Disjoint coproducts

Defines disjoint coproducts: coproducts where the intersection is initial and the coprojections
are monic.
Shows that a category with disjoint coproducts is `InitialMonoClass`.

## TODO

* Adapt this to the infinitary (small) version: This is one of the conditions in Giraud's theorem
  characterising sheaf topoi.
* Construct examples (and counterexamples?), e.g. Type, Vec.
* Define extensive categories, and show every extensive category has disjoint coproducts.
* Define coherent categories and use this to define positive coherent categories.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Category

variable {C : Type u} [Category.{v} C]

/--
Definition of `CoproductDisjoint` / `CoproductDisjoint` 的定义

English:
class CoproductDisjoint
  parameters: {ι : Type*} (X : ι -> C)
  axioms and operations (2):
    - nonempty_isInitial_of_ne({c : Cofan X} (hc : IsColimit c) {i j : ι} (_ : i != j) (s : PullbackCone (c.inj i) (c.inj j))) : IsLimit s -> Nonempty (IsInitial s.pt)
    - mono_inj({c : Cofan X} (hc : IsColimit c) (i : ι)) : Mono (c.inj i)

中文:
类 余productDisjoint
  参数: {ι : 类型} (X : ι -> C)
  公理与运算 (2 个):
    - nonempty_isInitial_of_ne({c : Cofan X} (hc : 是余极限 c) {i j : ι} (_ : i != j) (s : PullbackCone (c.inj i) (c.inj j))) : 是极限 s -> 非空 (IsInitial s.pt)
    - mono_inj({c : Cofan X} (hc : 是余极限 c) (i : ι)) : 单态射 (c.inj i)
-/
class CoproductDisjoint {ι : Type*} (X : ι -> C) : Prop where
  nonempty_isInitial_of_ne {c : Cofan X} (hc : IsColimit c) {i j : ι} (_ : i != j)
    (s : PullbackCone (c.inj i) (c.inj j)) :
    IsLimit s -> Nonempty (IsInitial s.pt)
  mono_inj {c : Cofan X} (hc : IsColimit c) (i : ι) : Mono (c.inj i)

section

variable {ι : Type*} {X : ι -> C}

/--
lemma `CoproductDisjoint.of_cofan` / 引理 `CoproductDisjoint.of_cofan`

English:
lemma CoproductDisjoint.of_cofan
  statement: {c : Cofan X} (hc : IsColimit c)
  proof: by
    let e := hd.uniqueUpToIso hc
    have heq (i) : d.inj i ≫ e.hom.hom = c.inj i := e.hom.w ⟨i⟩
    let u : t.pt ⟶ (s hij).pt := by
      refine PullbackCone.IsLimit.lift (hs hij) t.fst t.snd ?_
      simp [← heq, t.condition_assoc]
    refine ⟨(H hij).ofIso ⟨(H hij).to t.pt, u, (H hij).hom_ext _ _, ?_⟩⟩
    refine PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [show (H hij).to (X i) = (s hij).fst from (H hij).hom_ext _ _, u]
    · simp [show (H hij).to (X j) = (s hij).snd from (H hij).hom_ext _ _, u]
  mono_inj {d} hd i := by
    rw [show d.inj i = c.inj i ≫ (hd.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

中文:
引理 余productDisjoint.of_cofan
  结论: {c : Cofan X} (hc : 是余极限 c)
  证明: by
    let e := hd.uniqueUpToIso hc
    have heq (i) : d.inj i ≫ e.hom.hom = c.inj i := e.hom.w ⟨i⟩
    let u : t.pt ⟶ (s hij).pt := by
      refine PullbackCone.IsLimit.lift (hs hij) t.fst t.snd ?_
      simp [← heq, t.condition_assoc]
    refine ⟨(H hij).ofIso ⟨(H hij).to t.pt, u, (H hij).hom_ext _ _, ?_⟩⟩
    refine PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [show (H hij).to (X i) = (s hij).fst from (H hij).hom_ext _ _, u]
    · simp [show (H hij).to (X j) = (s hij).snd from (H hij).hom_ext _ _, u]
  mono_inj {d} hd i := by
    rw [show d.inj i = c.inj i ≫ (hd.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, c.inj, condition_assoc, d.inj, e.hom.hom, e.hom.w, hd.uniqueUpToIso, hom_ext, mono_inj, t.condition_assoc, t.fst, t.pt, t.snd, uniqueUpToIso
-/
lemma CoproductDisjoint.of_cofan {c : Cofan X} (hc : IsColimit c)
    [forall i, Mono (c.inj i)]
    (s : forall {i j : ι} (_ : i != j), PullbackCone (c.inj i) (c.inj j))
    (hs : forall {i j : ι} (hij : i != j), IsLimit (s hij))
    (H : forall {i j : ι} (hij : i != j), IsInitial (s hij).pt) :
    CoproductDisjoint X where
  nonempty_isInitial_of_ne {d} hd {i j} hij t ht := by
    let e := hd.uniqueUpToIso hc
    have heq (i) : d.inj i ≫ e.hom.hom = c.inj i := e.hom.w ⟨i⟩
    let u : t.pt ⟶ (s hij).pt := by
      refine PullbackCone.IsLimit.lift (hs hij) t.fst t.snd ?_
      simp [← heq, t.condition_assoc]
    refine ⟨(H hij).ofIso ⟨(H hij).to t.pt, u, (H hij).hom_ext _ _, ?_⟩⟩
    refine PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [show (H hij).to (X i) = (s hij).fst from (H hij).hom_ext _ _, u]
    · simp [show (H hij).to (X j) = (s hij).snd from (H hij).hom_ext _ _, u]
  mono_inj {d} hd i := by
    rw [show d.inj i = c.inj i ≫ (hd.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

/--
lemma `CoproductDisjoint.of_hasCoproduct` / 引理 `CoproductDisjoint.of_hasCoproduct`

English:
lemma CoproductDisjoint.of_hasCoproduct
  statement: [HasCoproduct X] [forall i, Mono (Sigma.ι X i)]
  proof: have (i : ι) : Mono ((Cofan.mk (∐ X) (Sigma.ι X)).inj i) := inferInstanceAs Mono (Sigma.ι X i)
  .of_cofan (coproductIsCoproduct X) s hs H

中文:
引理 余productDisjoint.of_hasCoproduct
  结论: [HasCoproduct X] [对任意 i, 单态射 (依赖和类型.ι X i)]
  证明: have (i : ι) : Mono ((Cofan.mk (∐ X) (Sigma.ι X)).inj i) := inferInstanceAs Mono (Sigma.ι X i)
  .of_cofan (coproductIsCoproduct X) s hs H

Depends on / 依赖: Cofan.mk, coproductIsCoproduct, of_cofan
-/
lemma CoproductDisjoint.of_hasCoproduct [HasCoproduct X] [forall i, Mono (Sigma.ι X i)]
    (s : forall {i j : ι} (_ : i != j), PullbackCone (Sigma.ι X i) (Sigma.ι X j))
    (hs : forall {i j : ι} (hij : i != j), IsLimit (s hij))
    (H : forall {i j : ι} (hij : i != j), IsInitial (s hij).pt) :
    CoproductDisjoint X :=
have (i : ι) : Mono ((Cofan.mk (∐ X) (Sigma.ι X)).inj i) := inferInstanceAs Mono (Sigma.ι X i)
  .of_cofan (coproductIsCoproduct X) s hs H

variable [CoproductDisjoint X]

/--
lemma `_root_.CategoryTheory.Mono.of_coproductDisjoint` / 引理 `_root_.CategoryTheory.Mono.of_coproductDisjoint`

English:
lemma _root_.CategoryTheory.Mono.of_coproductDisjoint
  given: {c : Cofan X} (hc : IsColimit c) (i : ι)
  proof: CoproductDisjoint.mono_inj hc i

中文:
引理 _root_.范畴论.单态射.of_coproductDisjoint
  条件: {c : Cofan X} (hc : 是余极限 c) (i : ι)
  证明: CoproductDisjoint.mono_inj hc i

Depends on / 依赖: CoproductDisjoint, CoproductDisjoint.mono_inj, mono_inj
-/
lemma _root_.CategoryTheory.Mono.of_coproductDisjoint {c : Cofan X} (hc : IsColimit c) (i : ι) :
    Mono (c.inj i) :=
  CoproductDisjoint.mono_inj hc i

/--
Instance `_root_.CategoryTheory.Mono.ι_of_coproductDisjoint` / 实例 `_root_.CategoryTheory.Mono.ι_of_coproductDisjoint`

English:
instance _root_.CategoryTheory.Mono.ι_of_coproductDisjoint
  signature: [HasCoproduct X] (i : ι)
  body: CoproductDisjoint.mono_inj (colimit.isColimit _) i

中文:
实例 _root_.范畴论.单态射.ι_of_coproductDisjoint
  签名: [HasCoproduct X] (i : ι)
  定义体: CoproductDisjoint.mono_inj (colimit.isColimit _) i

Depends on / 依赖: CoproductDisjoint, CoproductDisjoint.mono_inj, colimit, colimit.isColimit, isColimit, mono_inj
-/
instance _root_.CategoryTheory.Mono.ι_of_coproductDisjoint [HasCoproduct X] (i : ι) :
    Mono (Sigma.ι X i) :=
  CoproductDisjoint.mono_inj (colimit.isColimit _) i

namespace IsInitial
variable {i j : ι} (hij : i != j)

/--
Definition of `ofCoproductDisjointOfIsColimitOfIsLimit` / `ofCoproductDisjointOfIsColimitOfIsLimit` 的定义

English:
definition ofCoproductDisjointOfIsColimitOfIsLimit
  signature: {c : Cofan X} (hc : IsColimit c)
  body: (CoproductDisjoint.nonempty_isInitial_of_ne hc hij _ hs).some

中文:
定义 ofCoproductDisjointOfIsColimitOfIsLimit
  签名: {c : Cofan X} (hc : 是余极限 c)
  定义体: (CoproductDisjoint.nonempty_isInitial_of_ne hc hij _ hs).some

Depends on / 依赖: CoproductDisjoint, CoproductDisjoint.nonempty_isInitial_of_ne, nonempty_isInitial_of_ne
-/
noncomputable def ofCoproductDisjointOfIsColimitOfIsLimit {c : Cofan X} (hc : IsColimit c)
    {s : PullbackCone (c.inj i) (c.inj j)} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc hij _ hs).some

/--
Definition of `ofCoproductDisjoint` / `ofCoproductDisjoint` 的定义

English:
definition ofCoproductDisjoint
  signature: [HasCoproduct X] [HasPullback (Sigma.ι X i) (Sigma.ι X j)]
  body: ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _)
    (pullback.isLimit (Sigma.ι X i) (Sigma.ι X j))

中文:
定义 ofCoproductDisjoint
  签名: [HasCoproduct X] [HasPullback (依赖和类型.ι X i) (依赖和类型.ι X j)]
  定义体: ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _)
    (pullback.isLimit (Sigma.ι X i) (Sigma.ι X j))

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLimit, ofCoproductDisjointOfIsColimitOfIsLimit, pullback, pullback.isLimit
-/
noncomputable def ofCoproductDisjoint [HasCoproduct X] [HasPullback (Sigma.ι X i) (Sigma.ι X j)] :
    IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _)
    (pullback.isLimit (Sigma.ι X i) (Sigma.ι X j))

/--
Definition of `ofCoproductDisjointOfIsColimit` / `ofCoproductDisjointOfIsColimit` 的定义

English:
definition ofCoproductDisjointOfIsColimit
  body: ofCoproductDisjointOfIsColimitOfIsLimit hij hc (pullback.isLimit (f i) (f j))

中文:
定义 ofCoproductDisjointOfIsColimit
  定义体: ofCoproductDisjointOfIsColimitOfIsLimit hij hc (pullback.isLimit (f i) (f j))

Depends on / 依赖: isLimit, ofCoproductDisjointOfIsColimitOfIsLimit, pullback, pullback.isLimit
-/
noncomputable def ofCoproductDisjointOfIsColimit
    {Z : C} {f : forall i, X i ⟶ Z} [HasPullback (f i) (f j)] (hc : IsColimit (Cofan.mk _ f)) :
    IsInitial (pullback (f i) (f j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij hc (pullback.isLimit (f i) (f j))

/--
Definition of `ofCoproductDisjointOfIsLimit` / `ofCoproductDisjointOfIsLimit` 的定义

English:
definition ofCoproductDisjointOfIsLimit
  body: ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _) hs

中文:
定义 ofCoproductDisjointOfIsLimit
  定义体: ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _) hs

Depends on / 依赖: colimit, colimit.isColimit, isColimit, ofCoproductDisjointOfIsColimitOfIsLimit
-/
noncomputable def ofCoproductDisjointOfIsLimit
    [HasCoproduct X] {s : PullbackCone (Sigma.ι X i) (Sigma.ι X j)} (hs : IsLimit s) :
    IsInitial s.pt :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _) hs

/--
Definition of `ofCoproductDisjointOfCommSq` / `ofCoproductDisjointOfCommSq` 的定义

English:
definition ofCoproductDisjointOfCommSq
  signature: [HasStrictInitialObjects C]
  body: .ofStrict (pullback.lift fst snd h)
    .ofCoproductDisjointOfIsColimitOfIsLimit hij hc (limit.isLimit _)

中文:
定义 ofCoproductDisjointOfCommSq
  签名: [有StrictInitialObjects C]
  定义体: .ofStrict (pullback.lift fst snd h)
    .ofCoproductDisjointOfIsColimitOfIsLimit hij hc (limit.isLimit _)

Depends on / 依赖: isLimit, limit.isLimit, ofCoproductDisjointOfIsColimitOfIsLimit, ofStrict, pullback, pullback.lift
-/
noncomputable def ofCoproductDisjointOfCommSq [HasStrictInitialObjects C]
    {c : Cofan X} (hc : IsColimit c) {Z : C} (fst : Z ⟶ X i) (snd : Z ⟶ X j)
    (h : fst ≫ c.inj i = snd ≫ c.inj j) [HasPullback (c.inj i) (c.inj j)] :
    Limits.IsInitial Z :=
.ofStrict (pullback.lift fst snd h)
    .ofCoproductDisjointOfIsColimitOfIsLimit hij hc (limit.isLimit _)

end IsInitial

/--
lemma `CoproductDisjoint.isPullback_of_isInitial` / 引理 `CoproductDisjoint.isPullback_of_isInitial`

English:
lemma CoproductDisjoint.isPullback_of_isInitial
  statement: {c : Cofan X} (hc : IsColimit c)
  proof: by
  refine .of_iso_pullback (by simp) ?_ ?_ ?_
  · refine hY.uniqueUpToIso ?_
    exact IsInitial.ofCoproductDisjointOfIsColimit hij hc
  · simp
  · simp

中文:
引理 余productDisjoint.isPullback_of_isInitial
  结论: {c : Cofan X} (hc : 是余极限 c)
  证明: by
  refine .of_iso_pullback (by simp) ?_ ?_ ?_
  · refine hY.uniqueUpToIso ?_
    exact IsInitial.ofCoproductDisjointOfIsColimit hij hc
  · simp
  · simp

Depends on / 依赖: Category, IsInitial, IsInitial.ofCoproductDisjointOfIsColimit, hY.uniqueUpToIso, ofCoproductDisjointOfIsColimit, of_iso_pullback, uniqueUpToIso
-/
lemma CoproductDisjoint.isPullback_of_isInitial {c : Cofan X} (hc : IsColimit c)
    {Y : C} (hY : IsInitial Y) {i j : ι} [HasPullback (c.inj i) (c.inj j)] (hij : i != j) :
    IsPullback (hY.to _) (hY.to _) (c.inj i) (c.inj j) := by
  refine .of_iso_pullback (by simp) ?_ ?_ ?_
  · refine hY.uniqueUpToIso ?_
    exact IsInitial.ofCoproductDisjointOfIsColimit hij hc
  · simp
  · simp

end

/--
Definition of `BinaryCoproductDisjoint` / `BinaryCoproductDisjoint` 的定义

English:
abbreviation BinaryCoproductDisjoint
  signature: (X Y : C)
  body: CoproductDisjoint (fun j : WalkingPair => (j.casesOn X Y : C))

中文:
缩写 BinaryCoproductDisjoint
  签名: (X Y : C)
  定义体: CoproductDisjoint (fun j : WalkingPair => (j.casesOn X Y : C))

Depends on / 依赖: CoproductDisjoint, WalkingPair, casesOn, j.casesOn
-/
abbrev BinaryCoproductDisjoint (X Y : C) :=
  CoproductDisjoint (fun j : WalkingPair => (j.casesOn X Y : C))

section

variable {X Y : C}

/--
lemma `BinaryCoproductDisjoint.of_binaryCofan` / 引理 `BinaryCoproductDisjoint.of_binaryCofan`

English:
lemma BinaryCoproductDisjoint.of_binaryCofan
  statement: {c : BinaryCofan X Y} (hc : IsColimit c)
  proof: by
  have (i : WalkingPair) : Mono (Cofan.inj c i) := by
    cases i
· exact inferInstanceAs Mono c.inl
· exact inferInstanceAs Mono c.inr
  refine .of_cofan hc (fun {i j} hij => ?_) (fun {i j} hij => ?_) (fun {i j} hij => ?_)
  · match i, j with
    | .left, .right => exact s
    | .right, .left => exact s.flip
  · dsimp
    split
    · exact hs
    · exact PullbackCone.flipIsLimit hs
  · dsimp; split <;> exact H

中文:
引理 BinaryCoproductDisjoint.of_binaryCofan
  结论: {c : BinaryCofan X Y} (hc : 是余极限 c)
  证明: by
  have (i : WalkingPair) : Mono (Cofan.inj c i) := by
    cases i
· exact inferInstanceAs Mono c.inl
· exact inferInstanceAs Mono c.inr
  refine .of_cofan hc (fun {i j} hij => ?_) (fun {i j} hij => ?_) (fun {i j} hij => ?_)
  · match i, j with
    | .left, .right => exact s
    | .right, .left => exact s.flip
  · dsimp
    split
    · exact hs
    · exact PullbackCone.flipIsLimit hs
  · dsimp; split <;> exact H

Depends on / 依赖: Cofan.inj, PullbackCone, PullbackCone.flipIsLimit, WalkingPair, c.inl, c.inr, flipIsLimit, of_cofan, s.flip
-/
lemma BinaryCoproductDisjoint.of_binaryCofan {c : BinaryCofan X Y} (hc : IsColimit c)
    [Mono c.inl] [Mono c.inr] {s : PullbackCone c.inl c.inr}
    (hs : IsLimit s) (H : IsInitial s.pt) :
    BinaryCoproductDisjoint X Y := by
  have (i : WalkingPair) : Mono (Cofan.inj c i) := by
    cases i
· exact inferInstanceAs Mono c.inl
· exact inferInstanceAs Mono c.inr
  refine .of_cofan hc (fun {i j} hij => ?_) (fun {i j} hij => ?_) (fun {i j} hij => ?_)
  · match i, j with
    | .left, .right => exact s
    | .right, .left => exact s.flip
  · dsimp
    split
    · exact hs
    · exact PullbackCone.flipIsLimit hs
  · dsimp; split <;> exact H

variable [BinaryCoproductDisjoint X Y]

/--
lemma `_root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint` / 引理 `_root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint`

English:
lemma _root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint
  statement: {c : BinaryCofan X Y}
  proof: .of_coproductDisjoint hc .left

中文:
引理 _root_.范畴论.单态射.cofanInl_of_binaryCoproductDisjoint
  结论: {c : BinaryCofan X Y}
  证明: .of_coproductDisjoint hc .left

Depends on / 依赖: of_coproductDisjoint
-/
lemma _root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  .of_coproductDisjoint hc .left

/--
lemma `_root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint` / 引理 `_root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint`

English:
lemma _root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint
  statement: {c : BinaryCofan X Y}
  proof: .of_coproductDisjoint hc .right

中文:
引理 _root_.范畴论.单态射.cofanInr_of_binaryCoproductDisjoint
  结论: {c : BinaryCofan X Y}
  证明: .of_coproductDisjoint hc .right

Depends on / 依赖: of_coproductDisjoint
-/
lemma _root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  .of_coproductDisjoint hc .right

/--
lemma `_root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left` / 引理 `_root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left`

English:
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left
  statement: {Z : C}
  proof: .of_coproductDisjoint hc .left

中文:
引理 _root_.范畴论.单态射.of_binaryCoproductDisjoint_left
  结论: {Z : C}
  证明: .of_coproductDisjoint hc .left

Depends on / 依赖: of_coproductDisjoint
-/
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left {Z : C}
    {f : X ⟶ Z} (g : Y ⟶ Z) (hc : IsColimit <| BinaryCofan.mk f g) : Mono f :=
  .of_coproductDisjoint hc .left

/--
lemma `_root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right` / 引理 `_root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right`

English:
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right
  statement: {Z : C}
  proof: .of_coproductDisjoint hc .right

中文:
引理 _root_.范畴论.单态射.of_binaryCoproductDisjoint_right
  结论: {Z : C}
  证明: .of_coproductDisjoint hc .right

Depends on / 依赖: of_coproductDisjoint
-/
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right {Z : C}
    (f : X ⟶ Z) {g : Y ⟶ Z} (hc : IsColimit <| BinaryCofan.mk f g) : Mono g :=
  .of_coproductDisjoint hc .right

/--
Instance `_root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoint` / 实例 `_root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoint`

English:
instance _root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoint
  signature: [HasBinaryCoproduct X Y]
  body: @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.left

中文:
实例 _root_.范畴论.单态射.inl_of_binaryCoproductDisjoint
  签名: [HasBinaryCoproduct X Y]
  定义体: @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.left

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
instance _root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoint [HasBinaryCoproduct X Y] :
    Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.left

/--
Instance `_root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoint` / 实例 `_root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoint`

English:
instance _root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoint
  signature: [HasBinaryCoproduct X Y]
  body: @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.right

中文:
实例 _root_.范畴论.单态射.inr_of_binaryCoproductDisjoint
  签名: [HasBinaryCoproduct X Y]
  定义体: @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.right

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
instance _root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoint [HasBinaryCoproduct X Y] :
    Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.right

namespace IsInitial

/--
Definition of `ofBinaryCoproductDisjointOfIsColimitOfIsLimit` / `ofBinaryCoproductDisjointOfIsColimitOfIsLimit` 的定义

English:
definition ofBinaryCoproductDisjointOfIsColimitOfIsLimit
  body: (CoproductDisjoint.nonempty_isInitial_of_ne hc (by simp) _ hs).some

中文:
定义 ofBinaryCoproductDisjointOfIsColimitOfIsLimit
  定义体: (CoproductDisjoint.nonempty_isInitial_of_ne hc (by simp) _ hs).some

Depends on / 依赖: CoproductDisjoint, CoproductDisjoint.nonempty_isInitial_of_ne, nonempty_isInitial_of_ne
-/
noncomputable def ofBinaryCoproductDisjointOfIsColimitOfIsLimit
    {c : BinaryCofan X Y} (hc : IsColimit c) {s : PullbackCone c.inl c.inr} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc (by simp) _ hs).some

/--
Definition of `ofBinaryCoproductDisjoint` / `ofBinaryCoproductDisjoint` 的定义

English:
definition ofBinaryCoproductDisjoint
  signature: [HasBinaryCoproduct X Y]
  body: ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

中文:
定义 ofBinaryCoproductDisjoint
  签名: [HasBinaryCoproduct X Y]
  定义体: ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLimit, ofBinaryCoproductDisjointOfIsColimitOfIsLimit, pullback, pullback.isLimit
-/
noncomputable def ofBinaryCoproductDisjoint [HasBinaryCoproduct X Y]
    [HasPullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr] :
    IsInitial (pullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

/--
Definition of `ofBinaryCoproductDisjointOfIsColimit` / `ofBinaryCoproductDisjointOfIsColimit` 的定义

English:
definition ofBinaryCoproductDisjointOfIsColimit
  signature: {Z : C}
  body: ofBinaryCoproductDisjointOfIsColimitOfIsLimit hc (pullback.isLimit f g)

中文:
定义 ofBinaryCoproductDisjointOfIsColimit
  签名: {Z : C}
  定义体: ofBinaryCoproductDisjointOfIsColimitOfIsLimit hc (pullback.isLimit f g)

Depends on / 依赖: isLimit, ofBinaryCoproductDisjointOfIsColimitOfIsLimit, pullback, pullback.isLimit
-/
noncomputable def ofBinaryCoproductDisjointOfIsColimit {Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (hc : IsColimit (BinaryCofan.mk f g)) :
    IsInitial (pullback f g) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit hc (pullback.isLimit f g)

/--
Definition of `ofBinaryCoproductDisjointOfIsLimit` / `ofBinaryCoproductDisjointOfIsLimit` 的定义

English:
definition ofBinaryCoproductDisjointOfIsLimit
  body: ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) hs

中文:
定义 ofBinaryCoproductDisjointOfIsLimit
  定义体: ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) hs

Depends on / 依赖: colimit, colimit.isColimit, isColimit, ofBinaryCoproductDisjointOfIsColimitOfIsLimit
-/
noncomputable def ofBinaryCoproductDisjointOfIsLimit
    [HasBinaryCoproduct X Y] (s : PullbackCone (coprod.inl : X ⟶ X ⨿ Y) coprod.inr)
    (hs : IsLimit s) : IsInitial s.pt :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) hs

end IsInitial

end

/--
Definition of `CoproductsOfShapeDisjoint` / `CoproductsOfShapeDisjoint` 的定义

English:
class CoproductsOfShapeDisjoint
  parameters: (C : Type*) [Category* C] (ι : Type*)
  axioms and operations (1):
    - coproductDisjoint((X : ι -> C)) : CoproductDisjoint X

中文:
类 余productsOfShapeDisjoint
  参数: (C : 类型) [范畴* C] (ι : 类型)
  公理与运算 (1 个):
    - coproductDisjoint((X : ι -> C)) : 余productDisjoint X
-/
class CoproductsOfShapeDisjoint (C : Type*) [Category* C] (ι : Type*) : Prop where
  coproductDisjoint (X : ι -> C) : CoproductDisjoint X

/--
Definition of `BinaryCoproductsDisjoint` / `BinaryCoproductsDisjoint` 的定义

English:
abbreviation BinaryCoproductsDisjoint
  signature: (C : Type*) [Category* C]
  body: CoproductsOfShapeDisjoint C WalkingPair

中文:
缩写 BinaryCoproductsDisjoint
  签名: (C : 类型) [范畴* C]
  定义体: CoproductsOfShapeDisjoint C WalkingPair

Depends on / 依赖: CoproductsOfShapeDisjoint, WalkingPair
-/
abbrev BinaryCoproductsDisjoint (C : Type*) [Category* C] : Prop :=
  CoproductsOfShapeDisjoint C WalkingPair

attribute [instance 999] CoproductsOfShapeDisjoint.coproductDisjoint

/--
lemma `BinaryCoproductsDisjoint.mk` / 引理 `BinaryCoproductsDisjoint.mk`

English:
lemma BinaryCoproductsDisjoint.mk
  given: (H : forall (X Y : C), BinaryCoproductDisjoint X Y)
  proof: by
    convert! H (X .left) (X .right) using 2
    casesm WalkingPair <;> simp

中文:
引理 BinaryCoproductsDisjoint.mk
  条件: (H : 对任意 (X Y : C), BinaryCoproductDisjoint X Y)
  证明: by
    convert! H (X .left) (X .right) using 2
    casesm WalkingPair <;> simp

Depends on / 依赖: WalkingPair, casesm, convert
-/
lemma BinaryCoproductsDisjoint.mk (H : forall (X Y : C), BinaryCoproductDisjoint X Y) :
    BinaryCoproductsDisjoint C where
  coproductDisjoint X := by
    convert! H (X .left) (X .right) using 2
    casesm WalkingPair <;> simp

/--
theorem `initialMonoClass_of_coproductsDisjoint` / 定理 `initialMonoClass_of_coproductsDisjoint`

English:
theorem initialMonoClass_of_coproductsDisjoint
  given: [BinaryCoproductsDisjoint C]
  proof: .of_binaryCoproductDisjoint_left (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }

中文:
定理 initialMonoClass_of_coproductsDisjoint
  条件: [BinaryCoproductsDisjoint C]
  证明: .of_binaryCoproductDisjoint_left (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }

Depends on / 依赖: BinaryCofan, CategoryStruct, CategoryTheory, CategoryTheory.CategoryStruct.id, Discrete, Discrete.casesOn, WalkingPair, WalkingPair.casesOn, WalkingPair.right, casesOn, hI.hom_ext, hom_ext, id_comp, of_binaryCoproductDisjoint_left, s.inr, symm.trans
-/
theorem initialMonoClass_of_coproductsDisjoint [BinaryCoproductsDisjoint C] :
    InitialMonoClass C where
  isInitial_mono_from X hI :=
    .of_binaryCoproductDisjoint_left (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }

end CategoryTheory.Limits
