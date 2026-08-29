/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks


/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`IsPullback fst snd f g` is the proposition that
```
  P --fst--> X
  | |
 snd f
  | |
  v v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `IsPushout`.)

We provide the glue to go back and forth to the usual `IsLimit` API for pullbacks, and prove
`IsPullback (pullback.fst f g) (pullback.snd f g) f g`
for the usual `pullback f g` provided by the `HasLimit` API.
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
Definition of `IsPullback` / `IsPullback` 的定义

English:
structure IsPullback
  parameters: {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  extends: CommSq fst snd f g
  axioms and operations (1):
    - isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

中文:
结构 是拉回
  参数: {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  继承: 交换Sq fst snd f g
  公理与运算 (1 个):
    - isLimit' : 非空 (是极限 (PullbackCone.mk _ _ w))
-/
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop
    extends CommSq fst snd f g where
  /-- the pullback cone is a limit -/
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

/--
Definition of `IsPushout` / `IsPushout` 的定义

English:
structure IsPushout
  parameters: {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
  extends: CommSq f g inl inr
  axioms and operations (1):
    - isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

中文:
结构 是推出
  参数: {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
  继承: 交换Sq f g inl inr
  公理与运算 (1 个):
    - isColimit' : 非空 (是余极限 (PushoutCocone.mk _ _ w))
-/
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop
    extends CommSq f g inl inr where
  /-- the pushout cocone is a colimit -/
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (h : IsPullback fst snd f g)
  body: h.toCommSq.cone

@[simp]

中文:
定义 cone
  签名: (h : 是拉回 fst snd f g)
  定义体: h.toCommSq.cone

@[simp]

Depends on / 依赖: h.toCommSq.cone, toCommSq
-/
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone

@[simp]
/--
theorem `cone_fst` / 定理 `cone_fst`

English:
theorem cone_fst
  given: (h : IsPullback fst snd f g)
  statement: h.cone.fst = fst
  proof: rfl

@[simp]

中文:
定理 cone_fst
  条件: (h : 是拉回 fst snd f g)
  结论: h.cone.fst = fst
  证明: rfl

@[simp]
-/
theorem cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst :=
  rfl

@[simp]
/--
theorem `cone_snd` / 定理 `cone_snd`

English:
theorem cone_snd
  given: (h : IsPullback fst snd f g)
  statement: h.cone.snd = snd
  proof: rfl

中文:
定理 cone_snd
  条件: (h : 是拉回 fst snd f g)
  结论: h.cone.snd = snd
  证明: rfl
-/
theorem cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd :=
  rfl

/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: (h : IsPullback fst snd f g)
  body: h.isLimit'.some

中文:
定义 isLimit
  签名: (h : 是拉回 fst snd f g)
  定义体: h.isLimit'.some

Depends on / 依赖: h.isLimit, isLimit
-/
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.cone :=
  h.isLimit'.some

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  body: PullbackCone.IsLimit.lift hP.isLimit h k w

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: (hP : 是拉回 fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  定义体: PullbackCone.IsLimit.lift hP.isLimit h k w

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift, hP.isLimit, isLimit
-/
noncomputable def lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ P :=
  PullbackCone.IsLimit.lift hP.isLimit h k w

@[reassoc (attr := simp)]
/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  statement: (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  proof: PullbackCone.IsLimit.lift_fst hP.isLimit h k w

@[reassoc (attr := simp)]

中文:
引理 lift_fst
  结论: (hP : 是拉回 fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  证明: PullbackCone.IsLimit.lift_fst hP.isLimit h k w

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift_fst, hP.isLimit, isLimit, lift_fst
-/
lemma lift_fst (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h :=
  PullbackCone.IsLimit.lift_fst hP.isLimit h k w

@[reassoc (attr := simp)]
/--
lemma `lift_snd` / 引理 `lift_snd`

English:
lemma lift_snd
  statement: (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  proof: PullbackCone.IsLimit.lift_snd hP.isLimit h k w

中文:
引理 lift_snd
  结论: (hP : 是拉回 fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  证明: PullbackCone.IsLimit.lift_snd hP.isLimit h k w

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift_snd, hP.isLimit, isLimit, lift_snd
-/
lemma lift_snd (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k :=
  PullbackCone.IsLimit.lift_snd hP.isLimit h k w

/--
lemma `exists_lift` / 引理 `exists_lift`

English:
lemma exists_lift
  statement: (hP : IsPullback fst snd f g)
  proof: ⟨hP.lift h k w, by simp, by simp⟩

中文:
引理 存在_lift
  结论: (hP : 是拉回 fst snd f g)
  证明: ⟨hP.lift h k w, by simp, by simp⟩

Depends on / 依赖: hP.lift
-/
lemma exists_lift (hP : IsPullback fst snd f g)
    {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    exists (l : W ⟶ P), l ≫ fst = h ∧ l ≫ snd = k :=
  ⟨hP.lift h k w, by simp, by simp⟩

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P}
  proof: PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁

中文:
引理 hom_ext
  结论: (hP : 是拉回 fst snd f g) {W : C} {k l : W ⟶ P}
  证明: PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, hP.isLimit, hom_ext, isLimit
-/
lemma hom_ext (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P}
    (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l :=
  PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁

set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_isLimit` / 定理 `of_isLimit`

English:
theorem of_isLimit
  given: {c : PullbackCone f g} (h : Limits.IsLimit c)
  statement: IsPullback c.fst c.snd f g
  proof: { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by simp) (by simp))⟩ }

中文:
定理 of_isLimit
  条件: {c : PullbackCone f g} (h : Limits.是极限 c)
  结论: 是拉回 c.fst c.snd f g
  证明: { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by simp) (by simp))⟩ }

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, Iso.refl, Limits, Limits.PullbackCone.ext, PullbackCone, c.condition, condition, isLimit, ofIsoLimit
-/
theorem of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by simp) (by simp))⟩ }

/--
theorem `of_isLimit'` / 定理 `of_isLimit'`

English:
theorem of_isLimit'
  given: (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone)
  proof: of_isLimit h

中文:
定理 of_isLimit'
  条件: (w : 交换Sq fst snd f g) (h : Limits.是极限 w.cone)
  证明: of_isLimit h

Depends on / 依赖: of_isLimit
-/
theorem of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) :
    IsPullback fst snd f g :=
  of_isLimit h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_isLimit_cone` / 引理 `of_isLimit_cone`

English:
lemma of_isLimit_cone
  given: {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c)
  proof: by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩

中文:
引理 of_isLimit_cone
  条件: {D : WalkingCospan ⥤ C} {c : 锥 D} (hc : 是极限 c)
  证明: by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩

Depends on / 依赖: Cone.w, IsLimit, IsLimit.equivOfNatIsoOfIso, PullbackCone, PullbackCone.isoMk, equivOfNatIsoOfIso, isLimit, simp_rw
-/
lemma of_isLimit_cone {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsPullback (c.π.app .left) (c.π.app .right) (D.map WalkingCospan.Hom.inl)
      (D.map WalkingCospan.Hom.inr) where
  w := by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩

/--
lemma `hasPullback` / 引理 `hasPullback`

English:
lemma hasPullback
  given: (h : IsPullback fst snd f g)
  statement: HasPullback f g where
  proof: ⟨⟨h.cone, h.isLimit⟩⟩

中文:
引理 hasPullback
  条件: (h : 是拉回 fst snd f g)
  结论: HasPullback f g where
  证明: ⟨⟨h.cone, h.isLimit⟩⟩

Depends on / 依赖: h.cone, h.isLimit, isLimit
-/
lemma hasPullback (h : IsPullback fst snd f g) : HasPullback f g where
  exists_limit := ⟨⟨h.cone, h.isLimit⟩⟩

/--
theorem `of_hasPullback` / 定理 `of_hasPullback`

English:
theorem of_hasPullback
  given: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: of_isLimit (limit.isLimit (cospan f g))

中文:
定理 of_hasPullback
  条件: (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: of_isLimit (limit.isLimit (cospan f g))

Depends on / 依赖: cospan, isLimit, limit.isLimit, of_isLimit
-/
theorem of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
  of_isLimit (limit.isLimit (cospan f g))


section

variable (X Y)

variable {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y}

/--
Definition of `isoIsPullback` / `isoIsPullback` 的定义

English:
definition isoIsPullback
  signature: (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
  body: IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

@[reassoc (attr := simp)]

中文:
定义 isoIsPullback
  签名: (h : 是拉回 fst snd f g) (h' : 是拉回 fst' snd' f g)
  定义体: IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, h.isLimit, isLimit
-/
noncomputable def isoIsPullback (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    P ≅ P' :=
  IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

@[reassoc (attr := simp)]
/--
theorem `isoIsPullback_hom_fst` / 定理 `isoIsPullback_hom_fst`

English:
theorem isoIsPullback_hom_fst
  given: (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left

@[reassoc (attr := simp)]

中文:
定理 isoIsPullback_hom_fst
  条件: (h : 是拉回 fst snd f g) (h' : 是拉回 fst' snd' f g)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, WalkingCospan, WalkingCospan.left, conePointUniqueUpToIso_hom_comp, h.isLimit, isLimit
-/
theorem isoIsPullback_hom_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ fst' = fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left

@[reassoc (attr := simp)]
/--
theorem `isoIsPullback_hom_snd` / 定理 `isoIsPullback_hom_snd`

English:
theorem isoIsPullback_hom_snd
  given: (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right

@[reassoc (attr := simp)]

中文:
定理 isoIsPullback_hom_snd
  条件: (h : 是拉回 fst snd f g) (h' : 是拉回 fst' snd' f g)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_hom_comp, h.isLimit, isLimit
-/
theorem isoIsPullback_hom_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ snd' = snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right

@[reassoc (attr := simp)]
/--
theorem `isoIsPullback_inv_fst` / 定理 `isoIsPullback_inv_fst`

English:
theorem isoIsPullback_inv_fst
  given: (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
  proof: by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]

@[reassoc (attr := simp)]

中文:
定理 isoIsPullback_inv_fst
  条件: (h : 是拉回 fst snd f g) (h' : 是拉回 fst' snd' f g)
  证明: by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, isoIsPullback_hom_fst
-/
theorem isoIsPullback_inv_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ fst = fst' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]

@[reassoc (attr := simp)]
/--
theorem `isoIsPullback_inv_snd` / 定理 `isoIsPullback_inv_snd`

English:
theorem isoIsPullback_inv_snd
  given: (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
  proof: by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]

中文:
定理 isoIsPullback_inv_snd
  条件: (h : 是拉回 fst snd f g) (h' : 是拉回 fst' snd' f g)
  证明: by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, isoIsPullback_hom_snd
-/
theorem isoIsPullback_inv_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ snd = snd' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]

end

/--
Definition of `isoPullback` / `isoPullback` 的定义

English:
definition isoPullback
  signature: (h : IsPullback fst snd f g) [HasPullback f g]
  body: (limit.isoLimitCone ⟨_, h.isLimit⟩).symm

中文:
定义 isoPullback
  签名: (h : 是拉回 fst snd f g) [HasPullback f g]
  定义体: (limit.isoLimitCone ⟨_, h.isLimit⟩).symm

Depends on / 依赖: h.isLimit, isLimit, isoLimitCone, limit.isoLimitCone
-/
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.isLimit⟩).symm


set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `isoPullback_hom_fst` / 定理 `isoPullback_hom_fst`

English:
theorem isoPullback_hom_fst
  given: (h : IsPullback fst snd f g) [HasPullback f g]
  proof: by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

中文:
定理 isoPullback_hom_fst
  条件: (h : 是拉回 fst snd f g) [HasPullback f g]
  证明: by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

Depends on / 依赖: CommSq, CommSq.cone, isoPullback
-/
theorem isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst _ _ = fst := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `isoPullback_hom_snd` / 定理 `isoPullback_hom_snd`

English:
theorem isoPullback_hom_snd
  given: (h : IsPullback fst snd f g) [HasPullback f g]
  proof: by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]

中文:
定理 isoPullback_hom_snd
  条件: (h : 是拉回 fst snd f g) [HasPullback f g]
  证明: by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: CommSq, CommSq.cone, isoPullback
-/
theorem isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.snd _ _ = snd := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]
/--
theorem `isoPullback_inv_fst` / 定理 `isoPullback_inv_fst`

English:
theorem isoPullback_inv_fst
  given: (h : IsPullback fst snd f g) [HasPullback f g]
  proof: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]

中文:
定理 isoPullback_inv_fst
  条件: (h : 是拉回 fst snd f g) [HasPullback f g]
  证明: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ fst = pullback.fst _ _ := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
/--
theorem `isoPullback_inv_snd` / 定理 `isoPullback_inv_snd`

English:
theorem isoPullback_inv_snd
  given: (h : IsPullback fst snd f g) [HasPullback f g]
  proof: by simp [Iso.inv_comp_eq]

中文:
定理 isoPullback_inv_snd
  条件: (h : 是拉回 fst snd f g) [HasPullback f g]
  证明: by simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ snd = pullback.snd _ _ := by simp [Iso.inv_comp_eq]

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: (h : IsPushout f g inl inr)
  body: h.toCommSq.cocone

@[simp]

中文:
定义 cocone
  签名: (h : 是推出 f g inl inr)
  定义体: h.toCommSq.cocone

@[simp]

Depends on / 依赖: cocone, h.toCommSq.cocone, toCommSq
-/
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.toCommSq.cocone

@[simp]
/--
theorem `cocone_inl` / 定理 `cocone_inl`

English:
theorem cocone_inl
  given: (h : IsPushout f g inl inr)
  statement: h.cocone.inl = inl
  proof: rfl

@[simp]

中文:
定理 cocone_inl
  条件: (h : 是推出 f g inl inr)
  结论: h.cocone.inl = inl
  证明: rfl

@[simp]
-/
theorem cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl :=
  rfl

@[simp]
/--
theorem `cocone_inr` / 定理 `cocone_inr`

English:
theorem cocone_inr
  given: (h : IsPushout f g inl inr)
  statement: h.cocone.inr = inr
  proof: rfl

中文:
定理 cocone_inr
  条件: (h : 是推出 f g inl inr)
  结论: h.cocone.inr = inr
  证明: rfl
-/
theorem cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr :=
  rfl

/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: (h : IsPushout f g inl inr)
  body: h.isColimit'.some

中文:
定义 isColimit
  签名: (h : 是推出 f g inl inr)
  定义体: h.isColimit'.some

Depends on / 依赖: h.isColimit, isColimit
-/
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone :=
  h.isColimit'.some

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  body: PushoutCocone.IsColimit.desc hP.isColimit h k w

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: (hP : 是推出 f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  定义体: PushoutCocone.IsColimit.desc hP.isColimit h k w

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.desc, hP.isColimit, isColimit
-/
noncomputable def desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : P ⟶ W :=
  PushoutCocone.IsColimit.desc hP.isColimit h k w

@[reassoc (attr := simp)]
/--
lemma `inl_desc` / 引理 `inl_desc`

English:
lemma inl_desc
  statement: (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  proof: PushoutCocone.IsColimit.inl_desc hP.isColimit h k w

@[reassoc (attr := simp)]

中文:
引理 inl_desc
  结论: (hP : 是推出 f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  证明: PushoutCocone.IsColimit.inl_desc hP.isColimit h k w

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.inl_desc, hP.isColimit, inl_desc, isColimit
-/
lemma inl_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h :=
  PushoutCocone.IsColimit.inl_desc hP.isColimit h k w

@[reassoc (attr := simp)]
/--
lemma `inr_desc` / 引理 `inr_desc`

English:
lemma inr_desc
  statement: (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  proof: PushoutCocone.IsColimit.inr_desc hP.isColimit h k w

中文:
引理 inr_desc
  结论: (hP : 是推出 f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
  证明: PushoutCocone.IsColimit.inr_desc hP.isColimit h k w

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.inr_desc, hP.isColimit, inr_desc, isColimit
-/
lemma inr_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k :=
  PushoutCocone.IsColimit.inr_desc hP.isColimit h k w

/--
lemma `exists_desc` / 引理 `exists_desc`

English:
lemma exists_desc
  statement: (hP : IsPushout f g inl inr)
  proof: ⟨hP.desc h k w, by simp, by simp⟩

中文:
引理 存在_desc
  结论: (hP : 是推出 f g inl inr)
  证明: ⟨hP.desc h k w, by simp, by simp⟩

Depends on / 依赖: hP.desc
-/
lemma exists_desc (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) :
    exists (d : P ⟶ W), inl ≫ d = h ∧ inr ≫ d = k :=
  ⟨hP.desc h k w, by simp, by simp⟩

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W}
  proof: PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁

中文:
引理 hom_ext
  结论: (hP : 是推出 f g inl inr) {W : C} {k l : P ⟶ W}
  证明: PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.hom_ext, hP.isColimit, hom_ext, isColimit
-/
lemma hom_ext (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W}
    (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l :=
  PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁

set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_isColimit` / 定理 `of_isColimit`

English:
theorem of_isColimit
  given: {c : PushoutCocone f g} (h : Limits.IsColimit c)
  statement: IsPushout f g c.inl c.inr
  proof: { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by simp) (by simp))⟩ }

中文:
定理 of_isColimit
  条件: {c : PushoutCocone f g} (h : Limits.是余极限 c)
  结论: 是推出 f g c.inl c.inr
  证明: { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by simp) (by simp))⟩ }

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, Iso.refl, Limits, Limits.PushoutCocone.ext, PushoutCocone, c.condition, condition, isColimit, ofIsoColimit
-/
theorem of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by simp) (by simp))⟩ }

/--
theorem `of_isColimit'` / 定理 `of_isColimit'`

English:
theorem of_isColimit'
  given: (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone)
  proof: of_isColimit h

中文:
定理 of_isColimit'
  条件: (w : 交换Sq f g inl inr) (h : Limits.是余极限 w.cocone)
  证明: of_isColimit h

Depends on / 依赖: of_isColimit
-/
theorem of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) :
    IsPushout f g inl inr :=
  of_isColimit h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_isColimit_cocone` / 引理 `of_isColimit_cocone`

English:
lemma of_isColimit_cocone
  given: {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c)
  proof: by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩

中文:
引理 of_isColimit_cocone
  条件: {D : WalkingSpan ⥤ C} {c : 余锥 D} (hc : 是余极限 c)
  证明: by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩

Depends on / 依赖: Cocone, Cocone.w, IsColimit, IsColimit.equivOfNatIsoOfIso, PushoutCocone, PushoutCocone.isoMk, equivOfNatIsoOfIso, isColimit, simp_rw
-/
lemma of_isColimit_cocone {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd)
      (c.ι.app .left) (c.ι.app .right) where
  w := by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩

/--
lemma `hasPushout` / 引理 `hasPushout`

English:
lemma hasPushout
  given: (h : IsPushout f g inl inr)
  statement: HasPushout f g where
  proof: ⟨⟨h.cocone, h.isColimit⟩⟩

中文:
引理 hasPushout
  条件: (h : 是推出 f g inl inr)
  结论: HasPushout f g where
  证明: ⟨⟨h.cocone, h.isColimit⟩⟩

Depends on / 依赖: cocone, h.cocone, h.isColimit, isColimit
-/
lemma hasPushout (h : IsPushout f g inl inr) : HasPushout f g where
  exists_colimit := ⟨⟨h.cocone, h.isColimit⟩⟩

/--
theorem `of_hasPushout` / 定理 `of_hasPushout`

English:
theorem of_hasPushout
  given: (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
  proof: of_isColimit (colimit.isColimit (span f g))

中文:
定理 of_hasPushout
  条件: (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
  证明: of_isColimit (colimit.isColimit (span f g))

Depends on / 依赖: colimit, colimit.isColimit, isColimit, of_isColimit
-/
theorem of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl f g) (pushout.inr f g) :=
  of_isColimit (colimit.isColimit (span f g))

section

variable (X Y)
variable {P' : C} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}

/--
Definition of `isoIsPushout` / `isoIsPushout` 的定义

English:
definition isoIsPushout
  signature: (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr')
  body: IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit

@[reassoc (attr := simp)]

中文:
定义 isoIsPushout
  签名: (h : 是推出 f g inl inr) (h' : 是推出 f g inl' inr')
  定义体: IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, h.isColimit, isColimit
-/
noncomputable def isoIsPushout (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    P ≅ P' :=
  IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit

@[reassoc (attr := simp)]
/--
theorem `inl_isoIsPushout_hom` / 定理 `inl_isoIsPushout_hom`

English:
theorem inl_isoIsPushout_hom
  given: (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr')
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left

@[reassoc (attr := simp)]

中文:
定理 inl_isoIsPushout_hom
  条件: (h : 是推出 f g inl inr) (h' : 是推出 f g inl' inr')
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, WalkingSpan, WalkingSpan.left, comp_coconePointUniqueUpToIso_hom, h.isColimit, isColimit
-/
theorem inl_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl ≫ (h.isoIsPushout _ _ h').hom = inl' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left

@[reassoc (attr := simp)]
/--
theorem `inr_isoIsPushout_hom` / 定理 `inr_isoIsPushout_hom`

English:
theorem inr_isoIsPushout_hom
  given: (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr')
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right

@[reassoc (attr := simp)]

中文:
定理 inr_isoIsPushout_hom
  条件: (h : 是推出 f g inl inr) (h' : 是推出 f g inl' inr')
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, WalkingSpan, WalkingSpan.right, comp_coconePointUniqueUpToIso_hom, h.isColimit, isColimit
-/
theorem inr_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr ≫ (h.isoIsPushout _ _ h').hom = inr' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right

@[reassoc (attr := simp)]
/--
theorem `inl_isoIsPushout_inv` / 定理 `inl_isoIsPushout_inv`

English:
theorem inl_isoIsPushout_inv
  given: (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr')
  proof: by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]

@[reassoc (attr := simp)]

中文:
定理 inl_isoIsPushout_inv
  条件: (h : 是推出 f g inl inr) (h' : 是推出 f g inl' inr')
  证明: by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, inl_isoIsPushout_hom
-/
theorem inl_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl' ≫ (h.isoIsPushout _ _ h').inv = inl := by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]

@[reassoc (attr := simp)]
/--
theorem `inr_isoIsPushout_inv` / 定理 `inr_isoIsPushout_inv`

English:
theorem inr_isoIsPushout_inv
  given: (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr')
  proof: by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]

中文:
定理 inr_isoIsPushout_inv
  条件: (h : 是推出 f g inl inr) (h' : 是推出 f g inl' inr')
  证明: by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, inr_isoIsPushout_hom
-/
theorem inr_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr' ≫ (h.isoIsPushout _ _ h').inv = inr := by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]

end

/--
Definition of `isoPushout` / `isoPushout` 的定义

English:
definition isoPushout
  signature: (h : IsPushout f g inl inr) [HasPushout f g]
  body: (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm

中文:
定义 isoPushout
  签名: (h : 是推出 f g inl inr) [HasPushout f g]
  定义体: (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm

Depends on / 依赖: colimit, colimit.isoColimitCocone, h.isColimit, isColimit, isoColimitCocone
-/
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inl_isoPushout_inv` / 定理 `inl_isoPushout_inv`

English:
theorem inl_isoPushout_inv
  given: (h : IsPushout f g inl inr) [HasPushout f g]
  proof: by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

中文:
定理 inl_isoPushout_inv
  条件: (h : 是推出 f g inl inr) [HasPushout f g]
  证明: by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

Depends on / 依赖: CommSq, CommSq.cocone, cocone, isoPushout
-/
theorem inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inl _ _ ≫ h.isoPushout.inv = inl := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inr_isoPushout_inv` / 定理 `inr_isoPushout_inv`

English:
theorem inr_isoPushout_inv
  given: (h : IsPushout f g inl inr) [HasPushout f g]
  proof: by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]

中文:
定理 inr_isoPushout_inv
  条件: (h : 是推出 f g inl inr) [HasPushout f g]
  证明: by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: CommSq, CommSq.cocone, cocone, isoPushout
-/
theorem inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inr _ _ ≫ h.isoPushout.inv = inr := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]
/--
theorem `inl_isoPushout_hom` / 定理 `inl_isoPushout_hom`

English:
theorem inl_isoPushout_hom
  given: (h : IsPushout f g inl inr) [HasPushout f g]
  proof: by simp [← Iso.eq_comp_inv]

@[reassoc (attr := simp)]

中文:
定理 inl_isoPushout_hom
  条件: (h : 是推出 f g inl inr) [HasPushout f g]
  证明: by simp [← Iso.eq_comp_inv]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv
-/
theorem inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inl ≫ h.isoPushout.hom = pushout.inl _ _ := by simp [← Iso.eq_comp_inv]

@[reassoc (attr := simp)]
/--
theorem `inr_isoPushout_hom` / 定理 `inr_isoPushout_hom`

English:
theorem inr_isoPushout_hom
  given: (h : IsPushout f g inl inr) [HasPushout f g]
  proof: by simp [← Iso.eq_comp_inv]

中文:
定理 inr_isoPushout_hom
  条件: (h : 是推出 f g inl inr) [HasPushout f g]
  证明: by simp [← Iso.eq_comp_inv]

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv
-/
theorem inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inr ≫ h.isoPushout.hom = pushout.inr _ _ := by simp [← Iso.eq_comp_inv]

end IsPushout

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (h : IsPullback fst snd f g)
  statement: IsPullback snd fst g f
  proof: of_isLimit (PullbackCone.flipIsLimit h.isLimit)

中文:
定理 flip
  条件: (h : 是拉回 fst snd f g)
  结论: 是拉回 snd fst g f
  证明: of_isLimit (PullbackCone.flipIsLimit h.isLimit)

Depends on / 依赖: PullbackCone, PullbackCone.flipIsLimit, flipIsLimit, h.isLimit, isLimit, of_isLimit
-/
theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_isLimit (PullbackCone.flipIsLimit h.isLimit)

/--
theorem `flip_iff` / 定理 `flip_iff`

English:
theorem flip_iff
  statement: IsPullback fst snd f g ↔ IsPullback snd fst g f
  proof: ⟨flip, flip⟩

中文:
定理 flip_iff
  结论: 是拉回 fst snd f g ↔ 是拉回 snd fst g f
  证明: ⟨flip, flip⟩

Depends on / 依赖: of_retract
-/
theorem flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f :=
  ⟨flip, flip⟩


/--
theorem `op` / 定理 `op`

English:
theorem op
  given: (h : IsPullback fst snd f g)
  statement: IsPushout g.op f.op snd.op fst.op
  proof: IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)

中文:
定理 op
  条件: (h : 是拉回 fst snd f g)
  结论: 是推出 g.op f.op snd.op fst.op
  证明: IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, IsPushout, IsPushout.of_isColimit, Limits, Limits.PullbackCone.isLimitEquivIsColimitOp, PullbackCone, coneOp, h.flip.cone, h.flip.isLimit, h.toCommSq.flip.coneOp, isLimit, isLimitEquivIsColimitOp, ofIsoColimit, of_isColimit, toCommSq
-/
theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)

/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  statement: {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)

中文:
定理 unop
  结论: {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, IsPushout, IsPushout.of_isColimit, Limits, Limits.PullbackCone.isLimitEquivIsColimitUnop, PullbackCone, coneUnop, h.flip.cone, h.flip.isLimit, h.toCommSq.flip.coneUnop, isLimit, isLimitEquivIsColimitUnop, ofIsoColimit, of_isColimit, toCommSq
-/
theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)

end IsPullback

namespace IsPushout
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (h : IsPushout f g inl inr)
  statement: IsPushout g f inr inl
  proof: of_isColimit (PushoutCocone.flipIsColimit h.isColimit)

中文:
定理 flip
  条件: (h : 是推出 f g inl inr)
  结论: 是推出 g f inr inl
  证明: of_isColimit (PushoutCocone.flipIsColimit h.isColimit)

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, flipIsColimit, h.isColimit, isColimit, of_isColimit
-/
theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_isColimit (PushoutCocone.flipIsColimit h.isColimit)

/--
theorem `flip_iff` / 定理 `flip_iff`

English:
theorem flip_iff
  statement: IsPushout f g inl inr ↔ IsPushout g f inr inl
  proof: ⟨flip, flip⟩

中文:
定理 flip_iff
  结论: 是推出 f g inl inr ↔ 是推出 g f inr inl
  证明: ⟨flip, flip⟩

Depends on / 依赖: P.of_retract, of_retract
-/
theorem flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl :=
  ⟨flip, flip⟩

/--
theorem `op` / 定理 `op`

English:
theorem op
  given: (h : IsPushout f g inl inr)
  statement: IsPullback inr.op inl.op g.op f.op
  proof: IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)

中文:
定理 op
  条件: (h : 是推出 f g inl inr)
  结论: 是拉回 inr.op inl.op g.op f.op
  证明: IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, IsPullback, IsPullback.of_isLimit, Limits, Limits.PushoutCocone.isColimitEquivIsLimitOp, P.of_retract, PushoutCocone, cocone, coconeOp, h.flip.cocone, h.flip.isColimit, h.toCommSq.flip.coconeOp, isColimit, isColimitEquivIsLimitOp, ofIsoLimit, of_isLimit, of_retract, toCommSq
-/
theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)

/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  statement: {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  proof: IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)

中文:
定理 unop
  结论: {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  证明: IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, IsPullback, IsPullback.of_isLimit, Limits, Limits.PushoutCocone.isColimitEquivIsLimitUnop, PushoutCocone, cocone, coconeUnop, h.flip.cocone, h.flip.isColimit, h.toCommSq.flip.coconeUnop, isColimit, isColimitEquivIsLimitUnop, ofIsoLimit, of_isLimit, of_retract, toCommSq
-/
theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)

end IsPushout

/--
lemma `IsPullback.op_iff` / 引理 `IsPullback.op_iff`

English:
lemma IsPullback.op_iff
  given: {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 是拉回.op_iff
  条件: {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma IsPullback.op_iff {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPullback inr.op inl.op g.op f.op ↔ IsPushout f g inl inr :=
  ⟨fun h => h.unop, fun h => h.op⟩

/--
lemma `IsPullback.unop_iff` / 引理 `IsPullback.unop_iff`

English:
lemma IsPullback.unop_iff
  given: {X Y Z P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  proof: ⟨fun h => h.op, fun h => h.unop⟩

中文:
引理 是拉回.unop_iff
  条件: {X Y Z P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  证明: ⟨fun h => h.op, fun h => h.unop⟩

Depends on / 依赖: h.op, h.unop
-/
lemma IsPullback.unop_iff {X Y Z P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPullback inr.unop inl.unop g.unop f.unop ↔ IsPushout f g inl inr :=
  ⟨fun h => h.op, fun h => h.unop⟩

/--
lemma `IsPushout.op_iff` / 引理 `IsPushout.op_iff`

English:
lemma IsPushout.op_iff
  given: {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 是推出.op_iff
  条件: {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma IsPushout.op_iff {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPushout g.op f.op snd.op fst.op ↔ IsPullback fst snd f g :=
  ⟨fun h => h.unop, fun h => h.op⟩

/--
lemma `IsPushout.unop_iff` / 引理 `IsPushout.unop_iff`

English:
lemma IsPushout.unop_iff
  given: {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: ⟨fun h => h.op, fun h => h.unop⟩

中文:
引理 是推出.unop_iff
  条件: {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: ⟨fun h => h.op, fun h => h.unop⟩

Depends on / 依赖: h.op, h.unop
-/
lemma IsPushout.unop_iff {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPushout g.unop f.unop snd.unop fst.unop ↔ IsPullback fst snd f g :=
  ⟨fun h => h.op, fun h => h.unop⟩

end CategoryTheory
