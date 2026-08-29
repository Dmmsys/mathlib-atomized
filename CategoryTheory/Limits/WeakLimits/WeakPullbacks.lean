/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakEqualizers

/-!
# Weak pullbacks

These are weak limits for diagrams of shape `WalkingCospan`.

If a category has binary products and weak equalizers, then it has weak pullbacks
(see `hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers`).

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {W X Y Z : C}

/--
Definition of `HasWeakPullback` / `HasWeakPullback` 的定义

English:
abbreviation HasWeakPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: HasWeakLimit (cospan f g)

中文:
缩写 HasWeakPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: HasWeakLimit (cospan f g)

Depends on / 依赖: HasWeakLimit, cospan
-/
abbrev HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasWeakLimit (cospan f g)

/--
Definition of `weakPullback` / `weakPullback` 的定义

English:
abbreviation weakPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  body: weakLimit (cospan f g)

中文:
缩写 weakPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  定义体: weakLimit (cospan f g)

Depends on / 依赖: cospan, weakLimit
-/
abbrev weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :=
  weakLimit (cospan f g)

/--
Definition of `weakPullback.cone` / `weakPullback.cone` 的定义

English:
abbreviation weakPullback.cone
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: weakLimit.cone (cospan f g)

中文:
缩写 weakPullback.cone
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: weakLimit.cone (cospan f g)

Depends on / 依赖: cospan, weakLimit, weakLimit.cone
-/
abbrev weakPullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakPullback f g] : PullbackCone f g :=
  weakLimit.cone (cospan f g)

/--
Definition of `weakPullback.fst` / `weakPullback.fst` 的定义

English:
abbreviation weakPullback.fst
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  body: weakLimit.π (cospan f g) WalkingCospan.left

中文:
缩写 weakPullback.fst
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  定义体: weakLimit.π (cospan f g) WalkingCospan.left

Depends on / 依赖: WalkingCospan, WalkingCospan.left, cospan, weakLimit
-/
abbrev weakPullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ X :=
  weakLimit.π (cospan f g) WalkingCospan.left

/--
Definition of `weakPullback.snd` / `weakPullback.snd` 的定义

English:
abbreviation weakPullback.snd
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  body: weakLimit.π (cospan f g) WalkingCospan.right

中文:
缩写 weakPullback.snd
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  定义体: weakLimit.π (cospan f g) WalkingCospan.right

Depends on / 依赖: WalkingCospan, WalkingCospan.right, cospan, weakLimit
-/
abbrev weakPullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ Y :=
  weakLimit.π (cospan f g) WalkingCospan.right

/--
Definition of `weakPullback.lift` / `weakPullback.lift` 的定义

English:
abbreviation weakPullback.lift
  signature: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
  body: weakLimit.lift _ (PullbackCone.mk h k w)

中文:
缩写 weakPullback.lift
  签名: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
  定义体: weakLimit.lift _ (PullbackCone.mk h k w)

Depends on / 依赖: PullbackCone, PullbackCone.mk, cat_disch, weakLimit, weakLimit.lift, weakPullback
-/
abbrev weakPullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ weakPullback f g :=
  weakLimit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `weakPullback.exists_lift` / 引理 `weakPullback.exists_lift`

English:
lemma weakPullback.exists_lift
  statement: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  proof: ⟨weakPullback.lift h k, by simp⟩

中文:
引理 weakPullback.存在_lift
  结论: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  证明: ⟨weakPullback.lift h k, by simp⟩

Depends on / 依赖: cat_disch, weakPullback, weakPullback.fst, weakPullback.lift, weakPullback.snd
-/
lemma weakPullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    exists (l : W ⟶ weakPullback f g),
    l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k :=
  ⟨weakPullback.lift h k, by simp⟩

/--
Definition of `weakPullback.isWeakLimit` / `weakPullback.isWeakLimit` 的定义

English:
abbreviation weakPullback.isWeakLimit
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  body: weakLimit.isWeakLimit (cospan f g)

@[simp]

中文:
缩写 weakPullback.isWeakLimit
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  定义体: weakLimit.isWeakLimit (cospan f g)

@[simp]

Depends on / 依赖: cospan, isWeakLimit, weakLimit, weakLimit.isWeakLimit
-/
abbrev weakPullback.isWeakLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (weakPullback.cone f g) :=
  weakLimit.isWeakLimit (cospan f g)

@[simp]
/--
theorem `weakLimit.pullbackConeFst_cone_cospan` / 定理 `weakLimit.pullbackConeFst_cone_cospan`

English:
theorem weakLimit.pullbackConeFst_cone_cospan
  statement: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 weakLimit.pullbackConeFst_cone_cospan
  结论: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem weakLimit.pullbackConeFst_cone_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.fst (weakLimit.cone (cospan f g)) = weakPullback.fst f g := rfl

@[simp]
/--
theorem `weakLimit.pullbackConeSnd_cone_cospan` / 定理 `weakLimit.pullbackConeSnd_cone_cospan`

English:
theorem weakLimit.pullbackConeSnd_cone_cospan
  statement: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: rfl

@[reassoc]

中文:
定理 weakLimit.pullbackConeSnd_cone_cospan
  结论: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: rfl

@[reassoc]
-/
theorem weakLimit.pullbackConeSnd_cone_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.snd (weakLimit.cone (cospan f g)) = weakPullback.snd f g := rfl

@[reassoc]
/--
theorem `weakPullback.lift_fst` / 定理 `weakPullback.lift_fst`

English:
theorem weakPullback.lift_fst
  statement: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: weakLimit.lift_π _ _

@[reassoc]

中文:
定理 weakPullback.lift_fst
  结论: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: weakLimit.lift_π _ _

@[reassoc]

Depends on / 依赖: weakLimit, weakLimit.lift_
-/
theorem weakPullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.fst f g = h :=
  weakLimit.lift_π _ _

@[reassoc]
/--
theorem `weakPullback.lift_snd` / 定理 `weakPullback.lift_snd`

English:
theorem weakPullback.lift_snd
  statement: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: weakLimit.lift_π _ _

中文:
定理 weakPullback.lift_snd
  结论: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: weakLimit.lift_π _ _

Depends on / 依赖: weakLimit, weakLimit.lift_
-/
theorem weakPullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.snd f g = k :=
  weakLimit.lift_π _ _

/--
Definition of `weakPullback.lift'` / `weakPullback.lift'` 的定义

English:
definition weakPullback.lift'
  signature: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
  body: ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]

中文:
定义 weakPullback.lift'
  签名: {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
  定义体: ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]

Depends on / 依赖: lift_fst, lift_snd, weakPullback, weakPullback.lift, weakPullback.lift_fst, weakPullback.lift_snd
-/
def weakPullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
      { l : W ⟶ weakPullback f g //
      l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k } :=
  ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]
/--
theorem `weakPullback.condition` / 定理 `weakPullback.condition`

English:
theorem weakPullback.condition
  given: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
  proof: PullbackCone.condition _

中文:
定理 weakPullback.condition
  条件: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
  证明: PullbackCone.condition _

Depends on / 依赖: PullbackCone, PullbackCone.condition, condition
-/
theorem weakPullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] :
    weakPullback.fst f g ≫ f = weakPullback.snd f g ≫ g :=
  PullbackCone.condition _

/--
Definition of `weakPullback.map` / `weakPullback.map` 的定义

English:
abbreviation weakPullback.map
  signature: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
  body: weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

中文:
缩写 weakPullback.map
  签名: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
  定义体: weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

Depends on / 依赖: Category, Category.assoc, condition_assoc, weakPullback, weakPullback.condition_assoc, weakPullback.fst, weakPullback.lift, weakPullback.snd
-/
abbrev weakPullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasWeakPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    weakPullback f₁ f₂ ⟶ weakPullback g₁ g₂ :=
  weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

/--
Definition of `weakPullback.mapDesc` / `weakPullback.mapDesc` 的定义

English:
abbreviation weakPullback.mapDesc
  signature: {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
  body: weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

中文:
缩写 weakPullback.mapDesc
  签名: {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
  定义体: weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, id_comp, weakPullback, weakPullback.map
-/
abbrev weakPullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
    [HasWeakPullback (f ≫ i) (g ≫ i)] : weakPullback f g ⟶ weakPullback (f ≫ i) (g ≫ i) :=
  weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
Definition of `isWeakLimitAux` / `isWeakLimitAux` 的定义

English:
definition isWeakLimitAux
  signature: (t : PullbackCone f g) (lift : forall s : PullbackCone f g, s.pt ⟶ t.pt)
  body: { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl]; rw [← t.w WalkingCospan.Hom.inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

中文:
定义 isWeakLimitAux
  签名: (t : PullbackCone f g) (lift : 对任意 s : PullbackCone f g, s.pt ⟶ t.pt)
  定义体: { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl]; rw [← t.w WalkingCospan.Hom.inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

Depends on / 依赖: Category, Category.assoc, Option.casesOn, WalkingCospan, WalkingCospan.Hom.inl, WalkingPair, WalkingPair.casesOn, casesOn, fac_left, fac_right
-/
def isWeakLimitAux (t : PullbackCone f g) (lift : forall s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : forall s : PullbackCone f g, lift s ≫ t.snd = s.snd) : IsWeakLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl]; rw [← t.w WalkingCospan.Hom.inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

/--
Definition of `isWeakLimitAux'` / `isWeakLimitAux'` 的定义

English:
definition isWeakLimitAux'
  signature: (t : PullbackCone f g)
  body: PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

中文:
定义 isWeakLimitAux'
  签名: (t : PullbackCone f g)
  定义体: PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

Depends on / 依赖: PullbackCone, PullbackCone.isWeakLimitAux, create, isWeakLimitAux
-/
def isWeakLimitAux' (t : PullbackCone f g)
    (create :
      forall s : PullbackCone f g, { l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd}) :
    Limits.IsWeakLimit t :=
  PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

/--
Definition of `IsWeakLimit.mk` / `IsWeakLimit.mk` 的定义

English:
definition IsWeakLimit.mk
  signature: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
  body: isWeakLimitAux _ lift fac_left fac_right

中文:
定义 是WeakLimit.mk
  签名: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
  定义体: isWeakLimitAux _ lift fac_left fac_right

Depends on / 依赖: fac_left, fac_right, isWeakLimitAux
-/
def IsWeakLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : forall s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : forall s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : forall s : PullbackCone f g, lift s ≫ snd = s.snd) :
    IsWeakLimit (PullbackCone.mk fst snd eq) :=
  isWeakLimitAux _ lift fac_left fac_right

/--
Definition of `IsWeakLimit.lift` / `IsWeakLimit.lift` 的定义

English:
definition IsWeakLimit.lift
  signature: {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  body: ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]

中文:
定义 是WeakLimit.lift
  签名: {t : PullbackCone f g} (ht : 是WeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  定义体: ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]

Depends on / 依赖: PullbackCone, PullbackCone.mk, ht.lift
-/
def IsWeakLimit.lift {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
/--
lemma `IsWeakLimit.lift_fst` / 引理 `IsWeakLimit.lift_fst`

English:
lemma IsWeakLimit.lift_fst
  statement: {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
  proof: ht.fac _ _

@[reassoc (attr := simp)]

中文:
引理 是WeakLimit.lift_fst
  结论: {t : PullbackCone f g} (ht : 是WeakLimit t) {W : C} (h : W ⟶ X)
  证明: ht.fac _ _

@[reassoc (attr := simp)]

Depends on / 依赖: ht.fac
-/
lemma IsWeakLimit.lift_fst {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.fst t = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
/--
lemma `IsWeakLimit.lift_snd` / 引理 `IsWeakLimit.lift_snd`

English:
lemma IsWeakLimit.lift_snd
  statement: {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
  proof: ht.fac _ _

中文:
引理 是WeakLimit.lift_snd
  结论: {t : PullbackCone f g} (ht : 是WeakLimit t) {W : C} (h : W ⟶ X)
  证明: ht.fac _ _

Depends on / 依赖: ht.fac
-/
lemma IsWeakLimit.lift_snd {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.snd t = k :=
  ht.fac _ _

/--
Definition of `IsWeakLimit.lift'` / `IsWeakLimit.lift'` 的定义

English:
definition IsWeakLimit.lift'
  signature: {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  body: ⟨IsWeakLimit.lift ht h k w, by simp⟩

中文:
定义 是WeakLimit.lift'
  签名: {t : PullbackCone f g} (ht : 是WeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  定义体: ⟨IsWeakLimit.lift ht h k w, by simp⟩

Depends on / 依赖: IsWeakLimit, IsWeakLimit.lift
-/
def IsWeakLimit.lift' {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ t.pt // l ≫ PullbackCone.fst t = h ∧ l ≫ PullbackCone.snd t = k } :=
  ⟨IsWeakLimit.lift ht h k w, by simp⟩

/--
Definition of `mkSelfIsWeakLimit` / `mkSelfIsWeakLimit` 的定义

English:
definition mkSelfIsWeakLimit
  signature: {t : PullbackCone f g} (ht : IsWeakLimit t)
  body: IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

中文:
定义 mkSelfIsWeakLimit
  签名: {t : PullbackCone f g} (ht : 是WeakLimit t)
  定义体: IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

Depends on / 依赖: IsWeakLimit, IsWeakLimit.ofIsoWeakLimit, PullbackCone, PullbackCone.eta, ofIsoWeakLimit
-/
def mkSelfIsWeakLimit {t : PullbackCone f g} (ht : IsWeakLimit t) :
    IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

end PullbackCone

/--
Definition of `weakPullbackIsWeakPullback` / `weakPullbackIsWeakPullback` 的定义

English:
definition weakPullbackIsWeakPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  body: PullbackCone.mkSelfIsWeakLimit weakPullback.isWeakLimit f g

中文:
定义 weakPullbackIsWeakPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
  定义体: PullbackCone.mkSelfIsWeakLimit weakPullback.isWeakLimit f g

Depends on / 依赖: PullbackCone, PullbackCone.mkSelfIsWeakLimit, isWeakLimit, mkSelfIsWeakLimit, weakPullback, weakPullback.isWeakLimit
-/
def weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.snd f g)
    weakPullback.condition) :=
PullbackCone.mkSelfIsWeakLimit weakPullback.isWeakLimit f g

variable (C)

/--
Definition of `HasWeakPullbacks` / `HasWeakPullbacks` 的定义

English:
abbreviation HasWeakPullbacks
  body: HasWeakLimitsOfShape WalkingCospan C

中文:
缩写 HasWeakPullbacks
  定义体: HasWeakLimitsOfShape WalkingCospan C

Depends on / 依赖: HasWeakLimitsOfShape, WalkingCospan
-/
abbrev HasWeakPullbacks :=
  HasWeakLimitsOfShape WalkingCospan C

instance (priority := 100) HasWeakPullbacksOfHasPullbacks [HasPullbacks C] :
    HasWeakPullbacks C where

variable (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair` / 定理 `hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair`

English:
theorem hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair
  statement: [HasLimit (pair X Y)]
  proof: HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (weakEqualizer.ι (prod.fst ≫ f) (prod.snd ≫ g) ≫ prod.fst)
(weakEqualizer.ι _ _ ≫ prod.snd) by
          rw [Category.assoc]; rw [weakEqualizer.condition]
          simp
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s => weakEqu

中文:
定理 hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair
  结论: [有极限 (pair X Y)]
  证明: HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (weakEqualizer.ι (prod.fst ≫ f) (prod.snd ≫ g) ≫ prod.fst)
(weakEqualizer.ι _ _ ≫ prod.snd) by
          rw [Category.assoc]; rw [weakEqualizer.condition]
          simp
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s => weakEqu

Depends on / 依赖: Category, Category.assoc, HasWeakLimit, HasWeakLimit.mk, IsWeakLimit, PullbackCone, PullbackCone.IsWeakLimit.mk, PullbackCone.condition, PullbackCone.mk, condition, isWeakLimit, limit.lift_, prod.fst, prod.lift, prod.snd, weakEqualizer, weakEqualizer.condition, weakEqualizer.lift
-/
theorem hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair [HasLimit (pair X Y)]
    [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasWeakLimit (cospan f g) :=
  HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (weakEqualizer.ι (prod.fst ≫ f) (prod.snd ≫ g) ≫ prod.fst)
(weakEqualizer.ι _ _ ≫ prod.snd) by
          rw [Category.assoc]; rw [weakEqualizer.condition]
          simp
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s => weakEqualizer.lift
(prod.lift (s.π.app .left) (s.π.app .right)) by
            simp [limit.lift_π_assoc, PullbackCone.condition])
          (by simp) (by simp) }

attribute [local instance] hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair in
/--
theorem `hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers` / 定理 `hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers`

English:
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers
  proof: hasWeakLimit_of_iso (diagramIsoCospan F).symm

中文:
定理 hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers
  证明: hasWeakLimit_of_iso (diagramIsoCospan F).symm

Depends on / 依赖: diagramIsoCospan, hasWeakLimit_of_iso
-/
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers
    [HasBinaryProducts C] [HasWeakEqualizers C] : HasWeakPullbacks C where
  hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoCospan F).symm

end CategoryTheory.Limits
