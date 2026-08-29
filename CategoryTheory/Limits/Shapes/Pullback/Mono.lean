/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Pullbacks and monomorphisms

This file provides some results about interactions between pullbacks and monomorphisms, as well as
the dual statements between pushouts and epimorphisms.

## Main results
* Monomorphisms are stable under pullback. This is available using the `PullbackCone` API as
  `mono_fst_of_is_pullback_of_mono` and `mono_snd_of_is_pullback_of_mono`, and using the `pullback`
  API as `pullback.fst_of_mono` and `pullback.snd_of_mono`.

* A pullback cone is a limit iff its composition with a monomorphism is a limit. This is available
  as `IsLimitOfCompMono` and `pullbackIsPullbackOfCompMono` respectively.

* Monomorphisms admit kernel pairs, this is `has_kernel_pair_of_mono`.

The dual notions for pushouts are also available.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom PullbackCone

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

section Monomorphisms

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/--
theorem `mono_snd_of_is_pullback_of_mono` / 定理 `mono_snd_of_is_pullback_of_mono`

English:
theorem mono_snd_of_is_pullback_of_mono
  given: {t : PullbackCone f g} (ht : IsLimit t) [Mono f]
  proof: by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [condition]
  apply reassoc_of% i

中文:
定理 mono_snd_of_is_pullback_of_mono
  条件: {t : PullbackCone f g} (ht : IsLimit t) [Mono f]
  证明: by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [condition]
  apply reassoc_of% i

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.hom_ext, RespectsIso, RespectsIso.of_respects_arrow_iso, Retract, Retract.ofIso, cancel_mono, condition, e.symm, hom_ext, of_respects_arrow_iso, of_retract, reassoc_of
-/
theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [condition]
  apply reassoc_of% i

/--
theorem `mono_fst_of_is_pullback_of_mono` / 定理 `mono_fst_of_is_pullback_of_mono`

English:
theorem mono_fst_of_is_pullback_of_mono
  given: {t : PullbackCone f g} (ht : IsLimit t) [Mono g]
  proof: by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [← condition]
  apply reassoc_of% i

中文:
定理 mono_fst_of_is_pullback_of_mono
  条件: {t : PullbackCone f g} (ht : IsLimit t) [Mono g]
  证明: by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [← condition]
  apply reassoc_of% i

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.hom_ext, cancel_mono, condition, hom_ext, reassoc_of
-/
theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g]; rw [Category.assoc]; rw [Category.assoc]; rw [← condition]
  apply reassoc_of% i

/--
Definition of `isLimitMkIdId` / `isLimitMkIdId` 的定义

English:
definition isLimitMkIdId
  signature: (f : X ⟶ Y) [Mono f]
  body: IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

中文:
定义 isLimitMkIdId
  签名: (f : X ⟶ Y) [Mono f]
  定义体: IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

Depends on / 依赖: Category, Category.comp_id, IsLimit, IsLimit.mk, cancel_mono, comp_id, condition, s.condition, s.fst
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/--
theorem `mono_of_isLimitMkIdId` / 定理 `mono_of_isLimitMkIdId`

English:
theorem mono_of_isLimitMkIdId
  given: (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f))
  proof: ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

中文:
定理 mono_of_isLimitMkIdId
  条件: (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f))
  证明: ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitOfFactors` / `isLimitOfFactors` 的定义

English:
definition isLimitOfFactors
  signature: (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
  body: PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by -- Porting note: reassoc workaround
      rw [← Category.assoc]; rw [← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _

中文:
定义 isLimitOfFactors
  签名: (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
  定义体: PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by -- Porting note: reassoc workaround
      rw [← Category.assoc]; rw [← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _

Depends on / 依赖: Category, Category.assoc, IsLimit, Porting, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.isLimitAux, PullbackCone.mk, PullbackCone.mk_fst, PullbackCone.mk_snd, WalkingCospan, WalkingCospan.left, WalkingCospan.right, condition, exacts, hom_ext, hs.fac, hs.lift, isLimitAux, mk_fst
-/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
(cancel_mono h).1 by simp only [Category.assoc, hxh, hyh, s.condition])) :=
  PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by -- Porting note: reassoc workaround
      rw [← Category.assoc]; rw [← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun hr hr' => by
        apply PullbackCone.IsLimit.hom_ext hs <;>
              simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hr hr' ⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts [hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right]⟩⟩

/--
Definition of `isLimitOfCompMono` / `isLimitOfCompMono` 的定义

English:
definition isLimitOfCompMono
  signature: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
  body: by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

中文:
定义 isLimitOfCompMono
  签名: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
  定义体: by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, PullbackCone.isLimitAux, cancel_mono, condition, hom_ext, isLimitAux, s.condition, s.fst, s.snd
-/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [s.condition])) := by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PullbackCone

end Monomorphisms

/--
Instance `pullback.fst_of_mono` / 实例 `pullback.fst_of_mono`

English:
instance pullback.fst_of_mono
  signature: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g]
  body: PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

中文:
实例 pullback.fst_of_mono
  签名: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g]
  定义体: PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

Depends on / 依赖: PullbackCone, PullbackCone.mono_fst_of_is_pullback_of_mono, isLimit, limit.isLimit, mono_fst_of_is_pullback_of_mono
-/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst f g) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

/--
Instance `pullback.snd_of_mono` / 实例 `pullback.snd_of_mono`

English:
instance pullback.snd_of_mono
  signature: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f]
  body: PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

中文:
实例 pullback.snd_of_mono
  签名: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f]
  定义体: PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

Depends on / 依赖: PullbackCone, PullbackCone.mono_snd_of_is_pullback_of_mono, isLimit, limit.isLimit, mono_snd_of_is_pullback_of_mono
-/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd f g) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mono_pullback_to_prod` / 实例 `mono_pullback_to_prod`

English:
instance mono_pullback_to_prod
  signature: {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩

中文:
实例 mono_pullback_to_prod
  签名: {C : 类型} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩

Depends on / 依赖: prod.fst, prod.snd
-/
instance mono_pullback_to_prod {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩

/--
Definition of `pullbackIsPullbackOfCompMono` / `pullbackIsPullbackOfCompMono` 的定义

English:
definition pullbackIsPullbackOfCompMono
  signature: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
  body: PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

中文:
定义 pullbackIsPullbackOfCompMono
  签名: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
  定义体: PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

Depends on / 依赖: PullbackCone, PullbackCone.isLimitOfCompMono, cospan, isLimit, isLimitOfCompMono, limit.isLimit
-/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      -- Porting note: following used to be _
      (show (pullback.fst f g) ≫ f ≫ i = (pullback.snd f g) ≫ g ≫ i by
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition)) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

/--
Instance `hasPullback_of_comp_mono` / 实例 `hasPullback_of_comp_mono`

English:
instance hasPullback_of_comp_mono
  signature: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g]
  body: ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

中文:
实例 hasPullback_of_comp_mono
  签名: (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g]
  定义体: ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

Depends on / 依赖: pullbackIsPullbackOfCompMono
-/
instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

section

attribute [local instance] hasPullback_of_left_iso

variable (f : X ⟶ Z) (i : Z ⟶ W) [Mono i]

/--
Instance `hasPullback_of_right_factors_mono` / 实例 `hasPullback_of_right_factors_mono`

English:
instance hasPullback_of_right_factors_mono
  signature: : HasPullback i (f ≫ i)
  body: by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono (𝟙 Z) f i

中文:
实例 hasPullback_of_right_factors_mono
  签名: : HasPullback i (f ≫ i)
  定义体: by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono (𝟙 Z) f i

Depends on / 依赖: Category, Category.id_comp, hasPullback_of_comp_mono, id_comp
-/
instance hasPullback_of_right_factors_mono : HasPullback i (f ≫ i) := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono (𝟙 Z) f i

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `pullback_snd_iso_of_right_factors_mono` / 实例 `pullback_snd_iso_of_right_factors_mono`

English:
instance pullback_snd_iso_of_right_factors_mono
  signature: :
  body: by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  convert! (congrArg IsIso (show _ ≫ pullback.snd (𝟙 Z) f = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

中文:
实例 pullback_snd_iso_of_right_factors_mono
  签名: :
  定义体: by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  convert! (congrArg IsIso (show _ ≫ pullback.snd (𝟙 Z) f = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, WalkingCospan, WalkingCospan.right, convert, id_comp, limit.isoLimitCone_hom_, pullback, pullback.snd, pullbackIsPullbackOfCompMono
-/
instance pullback_snd_iso_of_right_factors_mono :
    IsIso (pullback.snd i (f ≫ i)) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  convert! (congrArg IsIso (show _ ≫ pullback.snd (𝟙 Z) f = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

attribute [local instance] hasPullback_of_right_iso

/--
Instance `hasPullback_of_left_factors_mono` / 实例 `hasPullback_of_left_factors_mono`

English:
instance hasPullback_of_left_factors_mono
  signature: : HasPullback (f ≫ i) i
  body: by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono f (𝟙 Z) i

中文:
实例 hasPullback_of_left_factors_mono
  签名: : HasPullback (f ≫ i) i
  定义体: by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono f (𝟙 Z) i

Depends on / 依赖: Category, Category.id_comp, hasPullback_of_comp_mono, id_comp
-/
instance hasPullback_of_left_factors_mono : HasPullback (f ≫ i) i := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono f (𝟙 Z) i

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `pullback_snd_iso_of_left_factors_mono` / 实例 `pullback_snd_iso_of_left_factors_mono`

English:
instance pullback_snd_iso_of_left_factors_mono
  signature: :
  body: by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  convert! (congrArg IsIso (show _ ≫ pullback.fst f (𝟙 Z) = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

中文:
实例 pullback_snd_iso_of_left_factors_mono
  签名: :
  定义体: by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  convert! (congrArg IsIso (show _ ≫ pullback.fst f (𝟙 Z) = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, WalkingCospan, WalkingCospan.left, convert, id_comp, limit.isoLimitCone_hom_, pullback, pullback.fst, pullbackIsPullbackOfCompMono
-/
instance pullback_snd_iso_of_left_factors_mono :
    IsIso (pullback.fst (f ≫ i) i) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  convert! (congrArg IsIso (show _ ≫ pullback.fst f (𝟙 Z) = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

end

section

open WalkingCospan

variable (f : X ⟶ Y) [Mono f]

/--
Instance `has_kernel_pair_of_mono` / 实例 `has_kernel_pair_of_mono`

English:
instance has_kernel_pair_of_mono
  signature: : HasPullback f f
  body: ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩

中文:
实例 has_kernel_pair_of_mono
  签名: : HasPullback f f
  定义体: ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩

Depends on / 依赖: PullbackCone, PullbackCone.isLimitMkIdId, isLimitMkIdId
-/
instance has_kernel_pair_of_mono : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩

/--
theorem `PullbackCone.fst_eq_snd_of_mono_eq` / 定理 `PullbackCone.fst_eq_snd_of_mono_eq`

English:
theorem PullbackCone.fst_eq_snd_of_mono_eq
  given: {f : X ⟶ Y} [Mono f] (t : PullbackCone f f)
  proof: (cancel_mono f).1 t.condition

中文:
定理 PullbackCone.fst_eq_snd_of_mono_eq
  条件: {f : X ⟶ Y} [Mono f] (t : PullbackCone f f)
  证明: (cancel_mono f).1 t.condition

Depends on / 依赖: cancel_mono, condition, t.condition
-/
theorem PullbackCone.fst_eq_snd_of_mono_eq {f : X ⟶ Y} [Mono f] (t : PullbackCone f f) :
    t.fst = t.snd :=
  (cancel_mono f).1 t.condition

/--
theorem `fst_eq_snd_of_mono_eq` / 定理 `fst_eq_snd_of_mono_eq`

English:
theorem fst_eq_snd_of_mono_eq
  statement: pullback.fst f f = pullback.snd f f
  proof: PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone

@[simp]

中文:
定理 fst_eq_snd_of_mono_eq
  结论: pullback.fst f f = pullback.snd f f
  证明: PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone

@[simp]

Depends on / 依赖: PullbackCone, PullbackCone.fst_eq_snd_of_mono_eq, cospan, fst_eq_snd_of_mono_eq, getLimitCone
-/
theorem fst_eq_snd_of_mono_eq : pullback.fst f f = pullback.snd f f :=
  PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone

@[simp]
/--
theorem `pullbackSymmetry_hom_of_mono_eq` / 定理 `pullbackSymmetry_hom_of_mono_eq`

English:
theorem pullbackSymmetry_hom_of_mono_eq
  statement: (pullbackSymmetry f f).hom = 𝟙 _
  proof: by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]

中文:
定理 pullbackSymmetry_hom_of_mono_eq
  结论: (pullbackSymmetry f f).hom = 𝟙 _
  证明: by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]

Depends on / 依赖: fst_eq_snd_of_mono_eq
-/
theorem pullbackSymmetry_hom_of_mono_eq : (pullbackSymmetry f f).hom = 𝟙 _ := by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
/--
lemma `PullbackCone.isIso_fst_of_mono_of_isLimit` / 引理 `PullbackCone.isIso_fst_of_mono_of_isLimit`

English:
lemma PullbackCone.isIso_fst_of_mono_of_isLimit
  given: {t : PullbackCone f f} (ht : IsLimit t)
  proof: by
  refine ⟨⟨PullbackCone.IsLimit.lift ht (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  apply PullbackCone.IsLimit.hom_ext ht
  · simp
  · simp [fst_eq_snd_of_mono_eq]

中文:
引理 PullbackCone.isIso_fst_of_mono_of_isLimit
  条件: {t : PullbackCone f f} (ht : IsLimit t)
  证明: by
  refine ⟨⟨PullbackCone.IsLimit.lift ht (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  apply PullbackCone.IsLimit.hom_ext ht
  · simp
  · simp [fst_eq_snd_of_mono_eq]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, fst_eq_snd_of_mono_eq, hom_ext
-/
lemma PullbackCone.isIso_fst_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.fst := by
  refine ⟨⟨PullbackCone.IsLimit.lift ht (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  apply PullbackCone.IsLimit.hom_ext ht
  · simp
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
/--
lemma `PullbackCone.isIso_snd_of_mono_of_isLimit` / 引理 `PullbackCone.isIso_snd_of_mono_of_isLimit`

English:
lemma PullbackCone.isIso_snd_of_mono_of_isLimit
  given: {t : PullbackCone f f} (ht : IsLimit t)
  proof: t.fst_eq_snd_of_mono_eq ▸ t.isIso_fst_of_mono_of_isLimit ht

中文:
引理 PullbackCone.isIso_snd_of_mono_of_isLimit
  条件: {t : PullbackCone f f} (ht : IsLimit t)
  证明: t.fst_eq_snd_of_mono_eq ▸ t.isIso_fst_of_mono_of_isLimit ht

Depends on / 依赖: fst_eq_snd_of_mono_eq, isIso_fst_of_mono_of_isLimit, t.fst_eq_snd_of_mono_eq, t.isIso_fst_of_mono_of_isLimit
-/
lemma PullbackCone.isIso_snd_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.snd :=
  t.fst_eq_snd_of_mono_eq ▸ t.isIso_fst_of_mono_of_isLimit ht

/--
Instance `isIso_fst_of_mono` / 实例 `isIso_fst_of_mono`

English:
instance isIso_fst_of_mono
  signature: : IsIso (pullback.fst f f)
  body: PullbackCone.isIso_fst_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

中文:
实例 isIso_fst_of_mono
  签名: : IsIso (pullback.fst f f)
  定义体: PullbackCone.isIso_fst_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

Depends on / 依赖: PullbackCone, PullbackCone.isIso_fst_of_mono_of_isLimit, cospan, getLimitCone, isIso_fst_of_mono_of_isLimit, isLimit
-/
instance isIso_fst_of_mono : IsIso (pullback.fst f f) :=
  PullbackCone.isIso_fst_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

/--
Instance `isIso_snd_of_mono` / 实例 `isIso_snd_of_mono`

English:
instance isIso_snd_of_mono
  signature: : IsIso (pullback.snd f f)
  body: PullbackCone.isIso_snd_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

中文:
实例 isIso_snd_of_mono
  签名: : IsIso (pullback.snd f f)
  定义体: PullbackCone.isIso_snd_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

Depends on / 依赖: PullbackCone, PullbackCone.isIso_snd_of_mono_of_isLimit, cospan, getLimitCone, isIso_snd_of_mono_of_isLimit, isLimit
-/
instance isIso_snd_of_mono : IsIso (pullback.snd f f) :=
  PullbackCone.isIso_snd_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit
end

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/--
theorem `epi_inr_of_is_pushout_of_epi` / 定理 `epi_inr_of_is_pushout_of_epi`

English:
theorem epi_inr_of_is_pushout_of_epi
  given: {t : PushoutCocone f g} (ht : IsColimit t) [Epi f]
  proof: ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩

中文:
定理 epi_inr_of_is_pushout_of_epi
  条件: {t : PushoutCocone f g} (ht : IsColimit t) [Epi f]
  证明: ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩

Depends on / 依赖: IsColimit, IsColimit.hom_ext, cancel_epi, condition_assoc, hom_ext, t.condition_assoc
-/
theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩

/--
theorem `epi_inl_of_is_pushout_of_epi` / 定理 `epi_inl_of_is_pushout_of_epi`

English:
theorem epi_inl_of_is_pushout_of_epi
  given: {t : PushoutCocone f g} (ht : IsColimit t) [Epi g]
  proof: ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩

中文:
定理 epi_inl_of_is_pushout_of_epi
  条件: {t : PushoutCocone f g} (ht : IsColimit t) [Epi g]
  证明: ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩

Depends on / 依赖: IsColimit, IsColimit.hom_ext, cancel_epi, condition_assoc, hom_ext, t.condition_assoc
-/
theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩

/--
Definition of `isColimitMkIdId` / `isColimitMkIdId` 的定义

English:
definition isColimitMkIdId
  signature: (f : X ⟶ Y) [Epi f]
  body: IsColimit.mk _ (fun s => s.inl) (fun _ => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁

中文:
定义 isColimitMkIdId
  签名: (f : X ⟶ Y) [Epi f]
  定义体: IsColimit.mk _ (fun s => s.inl) (fun _ => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁

Depends on / 依赖: Category, Category.id_comp, IsColimit, IsColimit.mk, cancel_epi, condition, id_comp, s.condition, s.inl
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun _ => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/--
theorem `epi_of_isColimitMkIdId` / 定理 `epi_of_isColimitMkIdId`

English:
theorem epi_of_isColimitMkIdId
  statement: (f : X ⟶ Y)
  proof: ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

中文:
定理 epi_of_isColimitMkIdId
  结论: (f : X ⟶ Y)
  证明: ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.desc
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitOfFactors` / `isColimitOfFactors` 的定义

English:
definition isColimitOfFactors
  signature: (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
  body: by -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
(cancel_epi h).1

中文:
定义 isColimitOfFactors
  签名: (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
  定义体: by -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
(cancel_epi h).1

Depends on / 依赖: Category, Category.assoc, IsColimit, Porting, PushoutCocone, PushoutCocone.isColimitAux, PushoutCocone.mk, around, cancel_epi, condition, hs.desc, hs.f, isColimitAux, reassoc, s.condition, s.inl, s.inr, t.condition, t.inl, t.inr
-/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
    (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    have reassoc₁ : h ≫ x ≫ inl s = f ≫ inl s := by -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
(cancel_epi h).1 by rw [reassoc₁, reassoc₂, s.condition])) :=
  PushoutCocone.isColimitAux' _ fun t => ⟨hs.desc (PushoutCocone.mk t.inl t.inr <| by
    rw [← hhx]; rw [← hhy]; rw [Category.assoc]; rw [Category.assoc]; rw [t.condition]),
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun hr hr' => by
        apply PushoutCocone.IsColimit.hom_ext hs
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr]
          symm
          exact hs.fac _ WalkingSpan.left
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr']
          symm
          exact hs.fac _ WalkingSpan.right⟩⟩

/--
Definition of `isColimitOfEpiComp` / `isColimitOfEpiComp` 的定义

English:
definition isColimitOfEpiComp
  signature: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
  body: by
  apply PushoutCocone.isColimitAux'
  intro s
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.sy

中文:
定义 isColimitOfEpiComp
  签名: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
  定义体: by
  apply PushoutCocone.isColimitAux'
  intro s
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.sy

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.desc, PushoutCocone.IsColimit.hom_ext, PushoutCocone.isColimitAux, cancel_epi, condition, hom_ext, isColimitAux, s.condition, s.inl, s.inr
-/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
    (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [Category.assoc]; rw [Category.assoc]; rw [s.condition])) := by
  apply PushoutCocone.isColimitAux'
  intro s
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PushoutCocone

/--
Instance `pushout.inl_of_epi` / 实例 `pushout.inl_of_epi`

English:
instance pushout.inl_of_epi
  signature: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g]
  body: PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

中文:
实例 pushout.inl_of_epi
  签名: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g]
  定义体: PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

Depends on / 依赖: PushoutCocone, PushoutCocone.epi_inl_of_is_pushout_of_epi, colimit, colimit.isColimit, epi_inl_of_is_pushout_of_epi, isColimit
-/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

/--
Instance `pushout.inr_of_epi` / 实例 `pushout.inr_of_epi`

English:
instance pushout.inr_of_epi
  signature: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f]
  body: PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

中文:
实例 pushout.inr_of_epi
  签名: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f]
  定义体: PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

Depends on / 依赖: PushoutCocone, PushoutCocone.epi_inr_of_is_pushout_of_epi, colimit, colimit.isColimit, epi_inr_of_is_pushout_of_epi, isColimit
-/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr _ _ : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `epi_coprod_to_pushout` / 实例 `epi_coprod_to_pushout`

English:
instance epi_coprod_to_pushout
  signature: {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩

中文:
实例 epi_coprod_to_pushout
  签名: {C : 类型} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩

Depends on / 依赖: coprod, coprod.inl, coprod.inr
-/
instance epi_coprod_to_pushout {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc (pushout.inl f g) (pushout.inr f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩

/--
Definition of `pushoutIsPushoutOfEpiComp` / `pushoutIsPushoutOfEpiComp` 的定义

English:
definition pushoutIsPushoutOfEpiComp
  signature: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
  body: PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))

中文:
定义 pushoutIsPushoutOfEpiComp
  签名: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
  定义体: PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitOfEpiComp, colimit, colimit.isColimit, isColimit, isColimitOfEpiComp
-/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
    (show (h ≫ f) ≫ pushout.inl f g = (h ≫ g) ≫ pushout.inr f g by
    simp only [Category.assoc]; rw [cancel_epi]; exact pushout.condition)) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))

/--
Instance `hasPushout_of_epi_comp` / 实例 `hasPushout_of_epi_comp`

English:
instance hasPushout_of_epi_comp
  signature: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g]
  body: ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

中文:
实例 hasPushout_of_epi_comp
  签名: (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g]
  定义体: ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

Depends on / 依赖: pushoutIsPushoutOfEpiComp
-/
instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

section

attribute [local instance] hasPushout_of_left_iso

variable (f : X ⟶ Z) (h : W ⟶ X) [Epi h]

/--
Instance `hasPushout_of_right_factors_epi` / 实例 `hasPushout_of_right_factors_epi`

English:
instance hasPushout_of_right_factors_epi
  signature: : HasPushout h (h ≫ f)
  body: by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp (𝟙 X) f h

中文:
实例 hasPushout_of_right_factors_epi
  签名: : HasPushout h (h ≫ f)
  定义体: by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp (𝟙 X) f h

Depends on / 依赖: Category, Category.comp_id, comp_id, hasPushout_of_epi_comp
-/
instance hasPushout_of_right_factors_epi : HasPushout h (h ≫ f) := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp (𝟙 X) f h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pushout_inr_iso_of_right_factors_epi` / 实例 `pushout_inr_iso_of_right_factors_epi`

English:
instance pushout_inr_iso_of_right_factors_epi
  signature: :
  body: by
  convert!
    (congrArg IsIso
          (show pushout.inr _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩
              WalkingSpan.right)).mp
      inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm

中文:
实例 pushout_inr_iso_of_right_factors_epi
  签名: :
  定义体: by
  convert!
    (congrArg IsIso
          (show pushout.inr _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩
              WalkingSpan.right)).mp
      inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm

Depends on / 依赖: Category, Category.comp_id, WalkingSpan, WalkingSpan.right, colimit, colimit.isoColimitCocone_, comp_id, convert, pushout, pushout.inr, pushoutIsPushoutOfEpiComp
-/
instance pushout_inr_iso_of_right_factors_epi :
    IsIso (pushout.inr _ _ : _ ⟶ pushout h (h ≫ f)) := by
  convert!
    (congrArg IsIso
          (show pushout.inr _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩
              WalkingSpan.right)).mp
      inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm

attribute [local instance] hasPushout_of_right_iso

/--
Instance `hasPushout_of_left_factors_epi` / 实例 `hasPushout_of_left_factors_epi`

English:
instance hasPushout_of_left_factors_epi
  signature: (f : X ⟶ Y)
  body: by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp f (𝟙 X) h

中文:
实例 hasPushout_of_left_factors_epi
  签名: (f : X ⟶ Y)
  定义体: by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp f (𝟙 X) h

Depends on / 依赖: Category, Category.comp_id, comp_id, hasPushout_of_epi_comp
-/
instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp f (𝟙 X) h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pushout_inl_iso_of_left_factors_epi` / 实例 `pushout_inl_iso_of_left_factors_epi`

English:
instance pushout_inl_iso_of_left_factors_epi
  signature: (f : X ⟶ Y)
  body: by
  convert!
    (congrArg IsIso
          (show pushout.inl _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩
              WalkingSpan.left)).mp
      inferInstance
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

中文:
实例 pushout_inl_iso_of_left_factors_epi
  签名: (f : X ⟶ Y)
  定义体: by
  convert!
    (congrArg IsIso
          (show pushout.inl _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩
              WalkingSpan.left)).mp
      inferInstance
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

Depends on / 依赖: Category, Category.comp_id, WalkingSpan, WalkingSpan.left, colimit, colimit.isoColimitCocone_, comp_id, convert, pushout, pushout.inl, pushoutIsPushoutOfEpiComp
-/
instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl _ _ : _ ⟶ pushout (h ≫ f) h) := by
  convert!
    (congrArg IsIso
          (show pushout.inl _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩
              WalkingSpan.left)).mp
      inferInstance
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

end

section

open WalkingSpan

variable (f : X ⟶ Y) [Epi f]

/--
Instance `has_cokernel_pair_of_epi` / 实例 `has_cokernel_pair_of_epi`

English:
instance has_cokernel_pair_of_epi
  signature: : HasPushout f f
  body: ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩

中文:
实例 has_cokernel_pair_of_epi
  签名: : HasPushout f f
  定义体: ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitMkIdId, isColimitMkIdId
-/
instance has_cokernel_pair_of_epi : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩

/--
theorem `PushoutCocone.inl_eq_inr_of_epi_eq` / 定理 `PushoutCocone.inl_eq_inr_of_epi_eq`

English:
theorem PushoutCocone.inl_eq_inr_of_epi_eq
  given: {f : X ⟶ Y} [Epi f] (t : PushoutCocone f f)
  proof: (cancel_epi f).1 t.condition

中文:
定理 PushoutCocone.inl_eq_inr_of_epi_eq
  条件: {f : X ⟶ Y} [Epi f] (t : PushoutCocone f f)
  证明: (cancel_epi f).1 t.condition

Depends on / 依赖: cancel_epi, condition, t.condition
-/
theorem PushoutCocone.inl_eq_inr_of_epi_eq {f : X ⟶ Y} [Epi f] (t : PushoutCocone f f) :
    t.inl = t.inr :=
  (cancel_epi f).1 t.condition

/--
theorem `inl_eq_inr_of_epi_eq` / 定理 `inl_eq_inr_of_epi_eq`

English:
theorem inl_eq_inr_of_epi_eq
  statement: pushout.inl f f = pushout.inr f f
  proof: PushoutCocone.inl_eq_inr_of_epi_eq (getColimitCocone (span f f)).cocone

@[simp]

中文:
定理 inl_eq_inr_of_epi_eq
  结论: pushout.inl f f = pushout.inr f f
  证明: PushoutCocone.inl_eq_inr_of_epi_eq (getColimitCocone (span f f)).cocone

@[simp]

Depends on / 依赖: PushoutCocone, PushoutCocone.inl_eq_inr_of_epi_eq, cocone, getColimitCocone, inl_eq_inr_of_epi_eq
-/
theorem inl_eq_inr_of_epi_eq : pushout.inl f f = pushout.inr f f :=
  PushoutCocone.inl_eq_inr_of_epi_eq (getColimitCocone (span f f)).cocone

@[simp]
/--
theorem `pullback_symmetry_hom_of_epi_eq` / 定理 `pullback_symmetry_hom_of_epi_eq`

English:
theorem pullback_symmetry_hom_of_epi_eq
  statement: (pushoutSymmetry f f).hom = 𝟙 _
  proof: by
  ext <;> simp [inl_eq_inr_of_epi_eq]

中文:
定理 pullback_symmetry_hom_of_epi_eq
  结论: (pushoutSymmetry f f).hom = 𝟙 _
  证明: by
  ext <;> simp [inl_eq_inr_of_epi_eq]

Depends on / 依赖: inl_eq_inr_of_epi_eq
-/
theorem pullback_symmetry_hom_of_epi_eq : (pushoutSymmetry f f).hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]

variable {f} in
/--
lemma `PushoutCocone.isIso_inl_of_epi_of_isColimit` / 引理 `PushoutCocone.isIso_inl_of_epi_of_isColimit`

English:
lemma PushoutCocone.isIso_inl_of_epi_of_isColimit
  given: {t : PushoutCocone f f} (ht : IsColimit t)
  proof: by
  refine ⟨⟨PushoutCocone.IsColimit.desc ht (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply PushoutCocone.IsColimit.hom_ext ht
  · simp
  · simp [inl_eq_inr_of_epi_eq]

中文:
引理 PushoutCocone.isIso_inl_of_epi_of_isColimit
  条件: {t : PushoutCocone f f} (ht : IsColimit t)
  证明: by
  refine ⟨⟨PushoutCocone.IsColimit.desc ht (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply PushoutCocone.IsColimit.hom_ext ht
  · simp
  · simp [inl_eq_inr_of_epi_eq]

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.desc, PushoutCocone.IsColimit.hom_ext, h.mem_map, hom_ext, inl_eq_inr_of_epi_eq, mem_map
-/
lemma PushoutCocone.isIso_inl_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inl := by
  refine ⟨⟨PushoutCocone.IsColimit.desc ht (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply PushoutCocone.IsColimit.hom_ext ht
  · simp
  · simp [inl_eq_inr_of_epi_eq]

variable {f} in
/--
lemma `PushoutCocone.isIso_inr_of_epi_of_isColimit` / 引理 `PushoutCocone.isIso_inr_of_epi_of_isColimit`

English:
lemma PushoutCocone.isIso_inr_of_epi_of_isColimit
  given: {t : PushoutCocone f f} (ht : IsColimit t)
  proof: t.inl_eq_inr_of_epi_eq ▸ t.isIso_inl_of_epi_of_isColimit ht

中文:
引理 PushoutCocone.isIso_inr_of_epi_of_isColimit
  条件: {t : PushoutCocone f f} (ht : IsColimit t)
  证明: t.inl_eq_inr_of_epi_eq ▸ t.isIso_inl_of_epi_of_isColimit ht

Depends on / 依赖: h.mem_incl_app, inl_eq_inr_of_epi_eq, isIso_inl_of_epi_of_isColimit, mem_incl_app, t.inl_eq_inr_of_epi_eq, t.isIso_inl_of_epi_of_isColimit
-/
lemma PushoutCocone.isIso_inr_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inr :=
  t.inl_eq_inr_of_epi_eq ▸ t.isIso_inl_of_epi_of_isColimit ht

/--
Instance `isIso_inl_of_epi` / 实例 `isIso_inl_of_epi`

English:
instance isIso_inl_of_epi
  signature: : IsIso (pushout.inl f f)
  body: PushoutCocone.isIso_inl_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

中文:
实例 isIso_inl_of_epi
  签名: : IsIso (pushout.inl f f)
  定义体: PushoutCocone.isIso_inl_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

Depends on / 依赖: PushoutCocone, PushoutCocone.isIso_inl_of_epi_of_isColimit, getColimitCocone, isColimit, isIso_inl_of_epi_of_isColimit
-/
instance isIso_inl_of_epi : IsIso (pushout.inl f f) :=
  PushoutCocone.isIso_inl_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

/--
Instance `isIso_inr_of_epi` / 实例 `isIso_inr_of_epi`

English:
instance isIso_inr_of_epi
  signature: : IsIso (pushout.inr f f)
  body: PushoutCocone.isIso_inr_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

中文:
实例 isIso_inr_of_epi
  签名: : IsIso (pushout.inr f f)
  定义体: PushoutCocone.isIso_inr_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

Depends on / 依赖: PushoutCocone, PushoutCocone.isIso_inr_of_epi_of_isColimit, getColimitCocone, isColimit, isIso_inr_of_epi_of_isColimit
-/
instance isIso_inr_of_epi : IsIso (pushout.inr f f) :=
  PushoutCocone.isIso_inr_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

end

end CategoryTheory.Limits
