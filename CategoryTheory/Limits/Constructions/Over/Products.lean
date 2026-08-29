/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_widePullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `Over B` has `J`-indexed products.

Note that the binary case is done separately to ensure defeqs with the pullback in the base
category.

## TODO

* Generalise from arbitrary products to arbitrary limits. This is done in Toric.
* Dualise to get the `Under X` results.
-/

@[expose] public section


universe w v u -- morphism levels before object levels. See note [category_theory universes].

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}
variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-!
### Binary products

In this section we construct binary products in `Over X` and binary coproducts in `Under X`
explicitly as the pullbacks and pushouts of binary (co)fans in the base category.

For `Over X`, one could construct these binary products from the general theory of arbitrary
products from the next section, i.e.
```
(Cone.postcomposeEquivalence (diagramIsoCospan _).symm).trans
  (Over.ConstructProducts.conesEquiv _ (pair (Over.mk f) (Over.mk g)))
```
but this gives worse defeqs.

For `Under X`, there is currently no general theory of arbitrary coproducts.
-/

namespace CategoryTheory.Limits
section Over
variable {f : Y ⟶ X} {g : Z ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback cones to `X` are the same thing as binary fans in `Over X`. -/
@[implicit_reducible, simps]
/--
Definition of `pullbackConeEquivBinaryFan` / `pullbackConeEquivBinaryFan` 的定义

English:
definition pullbackConeEquivBinaryFan
  signature: : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  body: .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_ | _ | _) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; simp [BinaryFan.ext]

中文:
定义 pullbackConeEquivBinaryFan
  签名: : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  定义体: .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_ | _ | _) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; simp [BinaryFan.ext]

Depends on / 依赖: Over.homMk, c.fst
-/
def pullbackConeEquivBinaryFan : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  functor.obj c := .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_ | _ | _) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; simp [BinaryFan.ext]

set_option backward.isDefEq.respectTransparency false in
/-- A binary fan in `Over X` is a limit if its corresponding pullback cone to `X` is a limit. -/
-- `IsLimit.ofConeEquiv` isn't used here because the lift it defines is `𝟙 _ ≫ pullback.lift`.
-- TODO: Define `IsLimit.copy`?
@[simps!]
/--
Definition of `IsLimit.pullbackConeEquivBinaryFanFunctor` / `IsLimit.pullbackConeEquivBinaryFanFunctor` 的定义

English:
definition IsLimit.pullbackConeEquivBinaryFanFunctor
  signature: {c : PullbackCone f g} (hc : IsLimit c)
  body: BinaryFan.isLimitMk
    -- TODO: Drop `BinaryFan.IsLimit.lift'`. Instead provide the lemmas it bundles separately.
    -- TODO: Define `abbrev BinaryFan.IsLimit (c : BinaryFan X Y) := IsLimit c` for dot notation?
    (fun s => Over.homMk (hc.lift <| pullbackConeEquivBinaryFan.inverse.obj s) <| by
      simpa using! s.fst.w)
    (fun s => Over.OverMorphism.ext (hc.fac _ _)) (fun s => Over.OverMorphism.ext (hc.fac _ _))
    fun s m e₁ e₂ => by
      ext1
      apply PullbackCone.IsLimit.hom_ext hc
      · simpa using! congr(($e₁).left)
      · simpa using! congr(($e₂).left)

中文:
定义 是极限.pullbackConeEquivBinaryFanFunctor
  签名: {c : PullbackCone f g} (hc : 是极限 c)
  定义体: BinaryFan.isLimitMk
    -- TODO: Drop `BinaryFan.IsLimit.lift'`. Instead provide the lemmas it bundles separately.
    -- TODO: Define `abbrev BinaryFan.IsLimit (c : BinaryFan X Y) := IsLimit c` for dot notation?
    (fun s => Over.homMk (hc.lift <| pullbackConeEquivBinaryFan.inverse.obj s) <| by
      simpa using! s.fst.w)
    (fun s => Over.OverMorphism.ext (hc.fac _ _)) (fun s => Over.OverMorphism.ext (hc.fac _ _))
    fun s m e₁ e₂ => by
      ext1
      apply PullbackCone.IsLimit.hom_ext hc
      · simpa using! congr(($e₁).left)
      · simpa using! congr(($e₂).left)

Depends on / 依赖: BinaryFan, BinaryFan.isLimitMk, isLimitMk
-/
def IsLimit.pullbackConeEquivBinaryFanFunctor {c : PullbackCone f g} (hc : IsLimit c) :
IsLimit pullbackConeEquivBinaryFan.functor.obj c :=
  BinaryFan.isLimitMk
    -- TODO: Drop `BinaryFan.IsLimit.lift'`. Instead provide the lemmas it bundles separately.
    -- TODO: Define `abbrev BinaryFan.IsLimit (c : BinaryFan X Y) := IsLimit c` for dot notation?
    (fun s => Over.homMk (hc.lift <| pullbackConeEquivBinaryFan.inverse.obj s) <| by
      simpa using! s.fst.w)
    (fun s => Over.OverMorphism.ext (hc.fac _ _)) (fun s => Over.OverMorphism.ext (hc.fac _ _))
    fun s m e₁ e₂ => by
      ext1
      apply PullbackCone.IsLimit.hom_ext hc
      · simpa using! congr(($e₁).left)
      · simpa using! congr(($e₂).left)

-- This could also be `(IsLimit.ofConeEquiv pullbackConeEquivBinaryFan.symm).symm hc`, but possibly
-- bad defeqs?
/--
Definition of `IsLimit.pullbackConeEquivBinaryFanInverse` / `IsLimit.pullbackConeEquivBinaryFanInverse` 的定义

English:
definition IsLimit.pullbackConeEquivBinaryFanInverse
  signature: {c : BinaryFan (Over.mk f) (.mk g)} (hc : IsLimit c)
  body: PullbackCone.IsLimit.mk
    (c.fst.w.trans c.snd.w.symm)
    (fun s => (hc.lift <| pullbackConeEquivBinaryFan.functor.obj s).left)
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
 fun s m hm₁ hm₂ => by
      change PullbackCone f g at s
      have := hc.uniq (pullbackConeEquivBinaryFan.functor.obj s) (Over.homMk m <| by
        simp [← hm₁, dsimp% c.fst.w])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).left)

中文:
定义 是极限.pullbackConeEquivBinaryFanInverse
  签名: {c : BinaryFan (Over.mk f) (.mk g)} (hc : 是极限 c)
  定义体: PullbackCone.IsLimit.mk
    (c.fst.w.trans c.snd.w.symm)
    (fun s => (hc.lift <| pullbackConeEquivBinaryFan.functor.obj s).left)
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
 fun s m hm₁ hm₂ => by
      change PullbackCone f g at s
      have := hc.uniq (pullbackConeEquivBinaryFan.functor.obj s) (Over.homMk m <| by
        simp [← hm₁, dsimp% c.fst.w])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).left)

Depends on / 依赖: IsLimit, Over.homMk, PullbackCone, PullbackCone.IsLimit.mk, c.fst.w, c.fst.w.trans, c.snd.w.symm, functor, hc.fac, hc.lift, hc.uniq, pullbackConeEquivBinaryFan, pullbackConeEquivBinaryFan.functor.obj
-/
def IsLimit.pullbackConeEquivBinaryFanInverse {c : BinaryFan (Over.mk f) (.mk g)} (hc : IsLimit c) :
IsLimit pullbackConeEquivBinaryFan.inverse.obj c :=
  PullbackCone.IsLimit.mk
    (c.fst.w.trans c.snd.w.symm)
    (fun s => (hc.lift <| pullbackConeEquivBinaryFan.functor.obj s).left)
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
    (fun s => by simpa only using! congr($(hc.fac _ _).left))
 fun s m hm₁ hm₂ => by
      change PullbackCone f g at s
      have := hc.uniq (pullbackConeEquivBinaryFan.functor.obj s) (Over.homMk m <| by
        simp [← hm₁, dsimp% c.fst.w])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).left)

end Over

section Under
variable {f : X ⟶ Y} {g : X ⟶ Z}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pushout cocones from `X` are the same thing as binary cofans in `Under X`. -/
@[simps]
/--
Definition of `pushoutCoconeEquivBinaryCofan` / `pushoutCoconeEquivBinaryCofan` 的定义

English:
definition pushoutCoconeEquivBinaryCofan
  signature: : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  body: .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.trans c.inr.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_ | _ | _) <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (fun f => by ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp)
  functor_unitIso_comp c := by ext; simp

中文:
定义 pushoutCoconeEquivBinaryCofan
  签名: : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  定义体: .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.trans c.inr.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_ | _ | _) <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (fun f => by ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp)
  functor_unitIso_comp c := by ext; simp

Depends on / 依赖: Under.homMk, c.inl
-/
def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  functor.obj c := .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.trans c.inr.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_ | _ | _) <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c => c.eta) (fun f => by ext; simp)
  counitIso := NatIso.ofComponents (fun X => BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp)
  functor_unitIso_comp c := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- A binary cofan in `Under X` is a colimit if its corresponding pushout cocone from `X` is a
colimit. -/
-- `IsColimit.ofCoconeEquiv` isn't used here because the lift it defines is `pushout.desc ≫ 𝟙 _`.
-- TODO: Define `IsColimit.copy`?
@[simps!]
/--
Definition of `IsColimit.pushoutCoconeEquivBinaryCofanFunctor` / `IsColimit.pushoutCoconeEquivBinaryCofanFunctor` 的定义

English:
definition IsColimit.pushoutCoconeEquivBinaryCofanFunctor
  signature: {c : PushoutCocone f g} (hc : IsColimit c)
  body: BinaryCofan.isColimitMk
    (fun s => Under.homMk
(hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.trans s.inr.w.symm))) by
        simpa using! s.inl.w)
    (fun s => Under.UnderMorphism.ext (hc.fac _ _)) (fun s => Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ => by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using! congr(($e₁).right)
    · simpa using! congr(($e₂).right)

中文:
定义 是余极限.pushoutCoconeEquivBinaryCofanFunctor
  签名: {c : PushoutCocone f g} (hc : 是余极限 c)
  定义体: BinaryCofan.isColimitMk
    (fun s => Under.homMk
(hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.trans s.inr.w.symm))) by
        simpa using! s.inl.w)
    (fun s => Under.UnderMorphism.ext (hc.fac _ _)) (fun s => Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ => by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using! congr(($e₁).right)
    · simpa using! congr(($e₂).right)

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimitMk, IsColimit, PushoutCocone, PushoutCocone.IsColimit.hom_ext, PushoutCocone.mk, Under.UnderMorphism.ext, Under.homMk, UnderMorphism, hc.desc, hc.fac, hom_ext, isColimitMk, s.inl.right, s.inl.w, s.inl.w.trans, s.inr.right, s.inr.w.symm
-/
def IsColimit.pushoutCoconeEquivBinaryCofanFunctor {c : PushoutCocone f g} (hc : IsColimit c) :
IsColimit pushoutCoconeEquivBinaryCofan.functor.obj c :=
  BinaryCofan.isColimitMk
    (fun s => Under.homMk
(hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.trans s.inr.w.symm))) by
        simpa using! s.inl.w)
    (fun s => Under.UnderMorphism.ext (hc.fac _ _)) (fun s => Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ => by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using! congr(($e₁).right)
    · simpa using! congr(($e₂).right)

set_option backward.defeqAttrib.useBackward true in
-- This could also be `(IsColimit.ofCoconeEquiv pushoutCoconeEquivBinaryCofan.symm).symm hc`,
-- but possibly bad defeqs?
/--
Definition of `IsColimit.pushoutCoconeEquivBinaryCofanInverse` / `IsColimit.pushoutCoconeEquivBinaryCofanInverse` 的定义

English:
definition IsColimit.pushoutCoconeEquivBinaryCofanInverse
  signature: {c : BinaryCofan (Under.mk f) (.mk g)}
  body: PushoutCocone.IsColimit.mk
    (c.inl.w.trans c.inr.w.symm)
    (fun s => (hc.desc <| pushoutCoconeEquivBinaryCofan.functor.obj s).right)
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
 fun s m hm₁ hm₂ => by
      change PushoutCocone f g at s
      have := hc.uniq (pushoutCoconeEquivBinaryCofan.functor.obj s) (Under.homMk m <| by
        simp [← hm₁, dsimp% c.inl.w_assoc])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).right)

中文:
定义 是余极限.pushoutCoconeEquivBinaryCofanInverse
  签名: {c : BinaryCofan (Under.mk f) (.mk g)}
  定义体: PushoutCocone.IsColimit.mk
    (c.inl.w.trans c.inr.w.symm)
    (fun s => (hc.desc <| pushoutCoconeEquivBinaryCofan.functor.obj s).right)
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
 fun s m hm₁ hm₂ => by
      change PushoutCocone f g at s
      have := hc.uniq (pushoutCoconeEquivBinaryCofan.functor.obj s) (Under.homMk m <| by
        simp [← hm₁, dsimp% c.inl.w_assoc])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).right)

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.mk, Under.homMk, c.inl.w.trans, c.inl.w_assoc, c.inr.w.symm, functor, hc.desc, hc.fac, hc.uniq, pushoutCoconeEquivBinaryCofan, pushoutCoconeEquivBinaryCofan.functor.obj, w_assoc
-/
def IsColimit.pushoutCoconeEquivBinaryCofanInverse {c : BinaryCofan (Under.mk f) (.mk g)}
(hc : IsColimit c) : IsColimit pushoutCoconeEquivBinaryCofan.inverse.obj c :=
  PushoutCocone.IsColimit.mk
    (c.inl.w.trans c.inr.w.symm)
    (fun s => (hc.desc <| pushoutCoconeEquivBinaryCofan.functor.obj s).right)
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
    (fun s => by simpa only using! congr($(hc.fac _ _).right))
 fun s m hm₁ hm₂ => by
      change PushoutCocone f g at s
      have := hc.uniq (pushoutCoconeEquivBinaryCofan.functor.obj s) (Under.homMk m <| by
        simp [← hm₁, dsimp% c.inl.w_assoc])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).right)

end Under
end Limits

namespace Over
section BinaryProduct
variable {X : C} {Y Z : Over X}

open Limits

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isPullback_of_binaryFan_isLimit` / 引理 `isPullback_of_binaryFan_isLimit`

English:
lemma isPullback_of_binaryFan_isLimit
  given: (c : BinaryFan Y Z) (hc : IsLimit c)
  proof: ⟨by simp, ⟨hc.pullbackConeEquivBinaryFanInverse⟩⟩

中文:
引理 isPullback_of_binaryFan_isLimit
  条件: (c : BinaryFan Y Z) (hc : 是极限 c)
  证明: ⟨by simp, ⟨hc.pullbackConeEquivBinaryFanInverse⟩⟩

Depends on / 依赖: hc.pullbackConeEquivBinaryFanInverse, pullbackConeEquivBinaryFanInverse
-/
lemma isPullback_of_binaryFan_isLimit (c : BinaryFan Y Z) (hc : IsLimit c) :
    IsPullback c.fst.left c.snd.left Y.hom Z.hom :=
  ⟨by simp, ⟨hc.pullbackConeEquivBinaryFanInverse⟩⟩

variable (Y Z) [HasPullback Y.hom Z.hom] [HasBinaryProduct Y Z]

set_option backward.isDefEq.respectTransparency false in
/-- The product of `Y` and `Z` in `Over X` is isomorphic to `Y ×ₓ Z`. -/
noncomputable
/--
Definition of `prodLeftIsoPullback` / `prodLeftIsoPullback` 的定义

English:
definition prodLeftIsoPullback
  signature: :
  body: (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

中文:
定义 prodLeftIsoPullback
  签名: :
  定义体: (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

Depends on / 依赖: Over.isPullback_of_binaryFan_isLimit, isPullback_of_binaryFan_isLimit, isoPullback, prodIsProd
-/
def prodLeftIsoPullback :
    (Y ⨯ Z).left ≅ pullback Y.hom Z.hom :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prodLeftIsoPullback_hom_fst` / 引理 `prodLeftIsoPullback_hom_fst`

English:
lemma prodLeftIsoPullback_hom_fst
  proof: IsPullback.isoPullback_hom_fst _

中文:
引理 prodLeftIsoPullback_hom_fst
  证明: IsPullback.isoPullback_hom_fst _
-/
lemma prodLeftIsoPullback_hom_fst :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.fst _ _ = (prod.fst (X := Y)).left :=
  IsPullback.isoPullback_hom_fst _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prodLeftIsoPullback_hom_snd` / 引理 `prodLeftIsoPullback_hom_snd`

English:
lemma prodLeftIsoPullback_hom_snd
  proof: IsPullback.isoPullback_hom_snd _

中文:
引理 prodLeftIsoPullback_hom_snd
  证明: IsPullback.isoPullback_hom_snd _
-/
lemma prodLeftIsoPullback_hom_snd :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.snd _ _ = (prod.snd (X := Y)).left :=
  IsPullback.isoPullback_hom_snd _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prodLeftIsoPullback_inv_fst` / 引理 `prodLeftIsoPullback_inv_fst`

English:
lemma prodLeftIsoPullback_inv_fst
  proof: IsPullback.isoPullback_inv_fst _

中文:
引理 prodLeftIsoPullback_inv_fst
  证明: IsPullback.isoPullback_inv_fst _

Depends on / 依赖: pullback, pullback.fst
-/
lemma prodLeftIsoPullback_inv_fst :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.fst (X := Y)).left = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prodLeftIsoPullback_inv_snd` / 引理 `prodLeftIsoPullback_inv_snd`

English:
lemma prodLeftIsoPullback_inv_snd
  proof: IsPullback.isoPullback_inv_snd _

中文:
引理 prodLeftIsoPullback_inv_snd
  证明: IsPullback.isoPullback_inv_snd _

Depends on / 依赖: pullback, pullback.snd
-/
lemma prodLeftIsoPullback_inv_snd :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.snd (X := Y)).left = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

end BinaryProduct

/-!
### Arbitrary products

In this section, we prove that `J`-indexed products in `Over X` correspond to `J`-indexed pullbacks
in `C`.
-/

namespace ConstructProducts

/--
Definition of `widePullbackDiagramOfDiagramOver` / `widePullbackDiagramOfDiagramOver` 的定义

English:
abbreviation widePullbackDiagramOfDiagramOver
  signature: (B : C) {J : Type w} (F : Discrete J ⥤ Over B)
  body: WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom

中文:
缩写 widePullbackDiagramOfDiagramOver
  签名: (B : C) {J : 类型 w} (F : 离散 J ⥤ Over B)
  定义体: WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom

Depends on / 依赖: F.obj, WidePullbackShape, WidePullbackShape.wideCospan, wideCospan
-/
abbrev widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/--
Definition of `conesEquivInverseObj` / `conesEquivInverseObj` 的定义

English:
definition conesEquivInverseObj
  signature: (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F)
  body: c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }

中文:
定义 conesEquivInverseObj
  签名: (B : C) {J : 类型 w} (F : 离散 J ⥤ Over B) (c : 锥 F)
  定义体: c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }

Depends on / 依赖: c.pt.left
-/
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F) where
  pt := c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/--
Definition of `conesEquivInverse` / `conesEquivInverse` 的定义

English:
definition conesEquivInverse
  signature: (B : C) {J : Type w} (F : Discrete J ⥤ Over B)
  body: conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        obtain - | j := j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }

中文:
定义 conesEquivInverse
  签名: (B : C) {J : 类型 w} (F : 离散 J ⥤ Over B)
  定义体: conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        obtain - | j := j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }

Depends on / 依赖: conesEquivInverseObj
-/
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F) where
  obj := conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        obtain - | j := j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }

-- Porting note: this should help with the additional `naturality` proof we now have to give in
-- `conesEquivFunctor`, but doesn't.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Discrete

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/--
Definition of `conesEquivFunctor` / `conesEquivFunctor` 的定义

English:
definition conesEquivFunctor
  signature: (B : C) {J : Type w} (F : Discrete J ⥤ Over B)
  body: { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; cat_disch } }
  map f := { hom := Over.homMk f.hom }

中文:
定义 conesEquivFunctor
  签名: (B : C) {J : 类型 w} (F : 离散 J ⥤ Over B)
  定义体: { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; cat_disch } }
  map f := { hom := Over.homMk f.hom }

Depends on / 依赖: Over.homMk, Over.mk, WidePullbackShape, WidePullbackShape.Hom.term
-/
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F where
  obj c :=
    { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; cat_disch } }
  map f := { hom := Over.homMk f.hom }

-- Porting note: unfortunately `aesop` can't cope with a `cases` rule here for the type synonym
-- `WidePullbackShape`.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WidePullbackShape
-- If this worked we could avoid the `rintro` in `conesEquivUnitIso`.

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
/--
Definition of `conesEquivUnitIso` / `conesEquivUnitIso` 的定义

English:
definition conesEquivUnitIso
  signature: (B : C) (F : Discrete J ⥤ Over B)
  body: NatIso.ofComponents fun _ => Cone.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> cat_disch)

中文:
定义 conesEquivUnitIso
  签名: (B : C) (F : 离散 J ⥤ Over B)
  定义体: NatIso.ofComponents fun _ => Cone.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> cat_disch)

Depends on / 依赖: Cone.ext, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅
      conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents fun _ => Cone.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- TODO: Can we add `:= by aesop` to the second arguments of `NatIso.ofComponents` and
-- `Cone.ext`?
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
/--
Definition of `conesEquivCounitIso` / `conesEquivCounitIso` 的定义

English:
definition conesEquivCounitIso
  signature: (B : C) (F : Discrete J ⥤ Over B)
  body: NatIso.ofComponents fun _ => Cone.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }

中文:
定义 conesEquivCounitIso
  签名: (B : C) (F : 离散 J ⥤ Over B)
  定义体: NatIso.ofComponents fun _ => Cone.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }

Depends on / 依赖: Cone.ext, NatIso, NatIso.ofComponents, Over.homMk, ofComponents
-/
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun _ => Cone.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
/--
Definition of `conesEquiv` / `conesEquiv` 的定义

English:
definition conesEquiv
  signature: (B : C) (F : Discrete J ⥤ Over B)
  body: conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

中文:
定义 conesEquiv
  签名: (B : C) (F : 离散 J ⥤ Over B)
  定义体: conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

Depends on / 依赖: conesEquivFunctor
-/
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F where
  functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

/--
theorem `has_over_limit_discrete_of_widePullback_limit` / 定理 `has_over_limit_discrete_of_widePullback_limit`

English:
theorem has_over_limit_discrete_of_widePullback_limit
  statement: {B : C} (F : Discrete J ⥤ Over B)
  proof: HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

中文:
定理 has_over_limit_discrete_of_widePullback_limit
  结论: {B : C} (F : 离散 J ⥤ Over B)
  证明: HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

Depends on / 依赖: HasLimit, HasLimit.mk, IsLimit, IsLimit.ofRightAdjoint, conesEquiv, isLimit, limit.isLimit, ofRightAdjoint, symm.toAdjunction, toAdjunction, widePullbackDiagramOfDiagramOver
-/
theorem has_over_limit_discrete_of_widePullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

/--
theorem `over_product_of_widePullback` / 定理 `over_product_of_widePullback`

English:
theorem over_product_of_widePullback
  given: [HasLimitsOfShape (WidePullbackShape J) C] {B : C}
  proof: { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }

中文:
定理 over_product_of_widePullback
  条件: [有形状极限 (WidePullbackShape J) C] {B : C}
  证明: { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }

Depends on / 依赖: has_limit, has_over_limit_discrete_of_widePullback_limit
-/
theorem over_product_of_widePullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }

/--
theorem `over_binaryProduct_of_pullback` / 定理 `over_binaryProduct_of_pullback`

English:
theorem over_binaryProduct_of_pullback
  given: [HasPullbacks C] {B : C}
  statement: HasBinaryProducts (Over B)
  proof: over_product_of_widePullback

中文:
定理 over_binaryProduct_of_pullback
  条件: [有Pullbacks C] {B : C}
  结论: HasBinaryProducts (Over B)
  证明: over_product_of_widePullback

Depends on / 依赖: over_product_of_widePullback
-/
theorem over_binaryProduct_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_widePullback

/--
theorem `over_products_of_widePullbacks` / 定理 `over_products_of_widePullbacks`

English:
theorem over_products_of_widePullbacks
  given: [HasWidePullbacks.{w} C] {B : C}
  proof: fun _ => over_product_of_widePullback

中文:
定理 over_products_of_widePullbacks
  条件: [HasWidePullbacks.{w} C] {B : C}
  证明: fun _ => over_product_of_widePullback

Depends on / 依赖: over_product_of_widePullback
-/
theorem over_products_of_widePullbacks [HasWidePullbacks.{w} C] {B : C} :
    HasProducts.{w} (Over B) :=
  fun _ => over_product_of_widePullback

/--
theorem `over_finiteProducts_of_finiteWidePullbacks` / 定理 `over_finiteProducts_of_finiteWidePullbacks`

English:
theorem over_finiteProducts_of_finiteWidePullbacks
  given: [HasFiniteWidePullbacks C] {B : C}
  proof: ⟨fun _ => over_product_of_widePullback⟩

中文:
定理 over_finiteProducts_of_finiteWidePullbacks
  条件: [有FiniteWidePullbacks C] {B : C}
  证明: ⟨fun _ => over_product_of_widePullback⟩

Depends on / 依赖: over_product_of_widePullback
-/
theorem over_finiteProducts_of_finiteWidePullbacks [HasFiniteWidePullbacks C] {B : C} :
    HasFiniteProducts (Over B) :=
  ⟨fun _ => over_product_of_widePullback⟩

end ConstructProducts

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `over_hasTerminal` / 定理 `over_hasTerminal`

English:
theorem over_hasTerminal
  given: (B : C)
  statement: HasTerminal (Over B) where
  proof: HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift s := Over.homMk s.pt.hom
          fac _ j := j.as.elim
          uniq s m _ := by ext; simpa using m.w } }

中文:
定理 over_hasTerminal
  条件: (B : C)
  结论: 有终止 (Over B) where
  证明: HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift s := Over.homMk s.pt.hom
          fac _ j := j.as.elim
          uniq s m _ := by ext; simpa using m.w } }

Depends on / 依赖: HasLimit, HasLimit.mk
-/
theorem over_hasTerminal (B : C) : HasTerminal (Over B) where
  has_limit F := HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift s := Over.homMk s.pt.hom
          fac _ j := j.as.elim
          uniq s m _ := by ext; simpa using m.w } }

end CategoryTheory.Over
