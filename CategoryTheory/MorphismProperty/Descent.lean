/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!
# Descent of morphism properties

Given morphism properties `P` and `Q` we say that `P` descends along `Q` (`P.DescendsAlong Q`),
if whenever `Q` holds for `X ⟶ Z`, `P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`.
Dually, we define `P.CodescendsAlong Q`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C]

variable {P Q W : MorphismProperty C}

/--
Definition of `DescendsAlong` / `DescendsAlong` 的定义

English:
class DescendsAlong
  parameters: (P Q : MorphismProperty C)
  axioms and operations (1):
    - of_isPullback({A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}) : IsPullback fst snd f g -> Q f -> P fst -> P g

中文:
类 DescendsAlong
  参数: (P Q : Morphism命题erty C)
  公理与运算 (1 个):
    - of_isPullback({A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}) : IsPullback fst snd f g -> Q f -> P fst -> P g

Depends on / 依赖: F.IsTriangulated, IsTriangulated, PreservesZeroMorphisms
-/
class DescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPullback {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g -> Q f -> P fst -> P g

section DescendsAlong

variable {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
lemma `of_isPullback_of_descendsAlong` / 引理 `of_isPullback_of_descendsAlong`

English:
lemma of_isPullback_of_descendsAlong
  statement: [P.DescendsAlong Q] (h : IsPullback fst snd f g)
  proof: DescendsAlong.of_isPullback h hf hfst

中文:
引理 of_isPullback_of_descendsAlong
  结论: [P.DescendsAlong Q] (h : IsPullback fst snd f g)
  证明: DescendsAlong.of_isPullback h hf hfst

Depends on / 依赖: DescendsAlong, DescendsAlong.of_isPullback, of_isPullback
-/
lemma of_isPullback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) (hfst : P fst) : P g :=
  DescendsAlong.of_isPullback h hf hfst

/--
lemma `iff_of_isPullback` / 引理 `iff_of_isPullback`

English:
lemma iff_of_isPullback
  statement: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g)
  proof: ⟨fun hfst => of_isPullback_of_descendsAlong h hf hfst, fun hf => P.of_isPullback h.flip hf⟩

中文:
引理 iff_of_isPullback
  结论: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g)
  证明: ⟨fun hfst => of_isPullback_of_descendsAlong h hf hfst, fun hf => P.of_isPullback h.flip hf⟩

Depends on / 依赖: Additive, F.Additive, F.IsTriangulated, IsTriangulated, P.of_isPullback, h.flip, of_isPullback, of_isPullback_of_descendsAlong
-/
lemma iff_of_isPullback [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) : P fst ↔ P g :=
  ⟨fun hfst => of_isPullback_of_descendsAlong h hf hfst, fun hf => P.of_isPullback h.flip hf⟩

/--
lemma `of_pullback_fst_of_descendsAlong` / 引理 `of_pullback_fst_of_descendsAlong`

English:
lemma of_pullback_fst_of_descendsAlong
  statement: [P.DescendsAlong Q] [HasPullback f g] (hf : Q f)
  proof: of_isPullback_of_descendsAlong (.of_hasPullback f g) hf hfst

中文:
引理 of_pullback_fst_of_descendsAlong
  结论: [P.DescendsAlong Q] [HasPullback f g] (hf : Q f)
  证明: of_isPullback_of_descendsAlong (.of_hasPullback f g) hf hfst

Depends on / 依赖: of_hasPullback, of_isPullback_of_descendsAlong
-/
lemma of_pullback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f)
    (hfst : P (pullback.fst f g)) : P g :=
  of_isPullback_of_descendsAlong (.of_hasPullback f g) hf hfst

/--
lemma `pullback_fst_iff` / 引理 `pullback_fst_iff`

English:
lemma pullback_fst_iff
  statement: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
  proof: iff_of_isPullback (.of_hasPullback f g) hf

中文:
引理 pullback_fst_iff
  结论: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
  证明: iff_of_isPullback (.of_hasPullback f g) hf

Depends on / 依赖: iff_of_isPullback, of_hasPullback
-/
lemma pullback_fst_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hf : Q f) : P (pullback.fst f g) ↔ P g :=
  iff_of_isPullback (.of_hasPullback f g) hf

/--
lemma `of_pullback_snd_of_descendsAlong` / 引理 `of_pullback_snd_of_descendsAlong`

English:
lemma of_pullback_snd_of_descendsAlong
  statement: [P.DescendsAlong Q] [HasPullback f g] (hg : Q g)
  proof: of_isPullback_of_descendsAlong (IsPullback.of_hasPullback f g).flip hg hsnd

中文:
引理 of_pullback_snd_of_descendsAlong
  结论: [P.DescendsAlong Q] [HasPullback f g] (hg : Q g)
  证明: of_isPullback_of_descendsAlong (IsPullback.of_hasPullback f g).flip hg hsnd

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, of_hasPullback, of_isPullback_of_descendsAlong
-/
lemma of_pullback_snd_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hg : Q g)
    (hsnd : P (pullback.snd f g)) : P f :=
  of_isPullback_of_descendsAlong (IsPullback.of_hasPullback f g).flip hg hsnd

/--
lemma `pullback_snd_iff` / 引理 `pullback_snd_iff`

English:
lemma pullback_snd_iff
  statement: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
  proof: iff_of_isPullback (IsPullback.of_hasPullback f g).flip hg

中文:
引理 pullback_snd_iff
  结论: [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
  证明: iff_of_isPullback (IsPullback.of_hasPullback f g).flip hg

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, iff_of_isPullback, of_hasPullback
-/
lemma pullback_snd_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hg : Q g) : P (pullback.snd f g) ↔ P f :=
  iff_of_isPullback (IsPullback.of_hasPullback f g).flip hg

/--
Instance `DescendsAlong.top` / 实例 `DescendsAlong.top`

English:
instance DescendsAlong.top
  signature: : (⊤ : MorphismProperty C).DescendsAlong Q where
  body: trivial

中文:
实例 DescendsAlong.top
  签名: : (⊤ : Morphism命题erty C).DescendsAlong Q where
  定义体: trivial
-/
instance DescendsAlong.top : (⊤ : MorphismProperty C).DescendsAlong Q where
  of_isPullback _ _ _ := trivial

/--
Instance `DescendsAlong.inf` / 实例 `DescendsAlong.inf`

English:
instance DescendsAlong.inf
  signature: [P.DescendsAlong Q] [W.DescendsAlong Q]
  body: ⟨DescendsAlong.of_isPullback h hg hfst.1, DescendsAlong.of_isPullback h hg hfst.2⟩

中文:
实例 DescendsAlong.inf
  签名: [P.DescendsAlong Q] [W.DescendsAlong Q]
  定义体: ⟨DescendsAlong.of_isPullback h hg hfst.1, DescendsAlong.of_isPullback h hg hfst.2⟩

Depends on / 依赖: DescendsAlong, DescendsAlong.of_isPullback, of_isPullback
-/
instance DescendsAlong.inf [P.DescendsAlong Q] [W.DescendsAlong Q] : (P ⊓ W).DescendsAlong Q where
  of_isPullback h hg hfst :=
    ⟨DescendsAlong.of_isPullback h hg hfst.1, DescendsAlong.of_isPullback h hg hfst.2⟩

/--
lemma `DescendsAlong.of_le` / 引理 `DescendsAlong.of_le`

English:
lemma DescendsAlong.of_le
  given: [P.DescendsAlong Q] (hle : W <= Q)
  statement: P.DescendsAlong W where
  proof: DescendsAlong.of_isPullback h (hle _ hg) hfst

中文:
引理 DescendsAlong.of_le
  条件: [P.DescendsAlong Q] (hle : W <= Q)
  结论: P.DescendsAlong W where
  证明: DescendsAlong.of_isPullback h (hle _ hg) hfst

Depends on / 依赖: DescendsAlong, DescendsAlong.of_isPullback, of_isPullback
-/
lemma DescendsAlong.of_le [P.DescendsAlong Q] (hle : W <= Q) : P.DescendsAlong W where
  of_isPullback h hg hfst := DescendsAlong.of_isPullback h (hle _ hg) hfst

/--
lemma `DescendsAlong.mk'` / 引理 `DescendsAlong.mk'`

English:
lemma DescendsAlong.mk'
  statement: [P.RespectsIso]
  proof: by
    have : HasPullback f g := h.hasPullback
    apply H hf
    rwa [← P.cancel_left_of_respectsIso h.isoPullback.hom, h.isoPullback_hom_fst]

中文:
引理 DescendsAlong.mk'
  结论: [P.RespectsIso]
  证明: by
    have : HasPullback f g := h.hasPullback
    apply H hf
    rwa [← P.cancel_left_of_respectsIso h.isoPullback.hom, h.isoPullback_hom_fst]

Depends on / 依赖: HasPullback, P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, h.hasPullback, h.isoPullback.hom, h.isoPullback_hom_fst, hasPullback, isoPullback, isoPullback_hom_fst
-/
lemma DescendsAlong.mk' [P.RespectsIso]
    (H : forall {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g],
      Q f -> P (pullback.fst f g) -> P g) :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : HasPullback f g := h.hasPullback
    apply H hf
    rwa [← P.cancel_left_of_respectsIso h.isoPullback.hom, h.isoPullback_hom_fst]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsStableUnderBaseChange]
  signature: [P.HasOfPrecompProperty Q] [P.RespectsRight Q]
  body: by
    apply P.of_precomp (W' := Q) _ _ (Q.of_isPullback h hf)
    rw [← h.1.1]
    exact RespectsRight.postcomp _ hf _ hfst

中文:
实例 [Q.IsStableUnderBaseChange]
  签名: [P.HasOfPrecomp命题erty Q] [P.RespectsRight Q]
  定义体: by
    apply P.of_precomp (W' := Q) _ _ (Q.of_isPullback h hf)
    rw [← h.1.1]
    exact RespectsRight.postcomp _ hf _ hfst

Depends on / 依赖: P.of_precomp, Q.of_isPullback, RespectsRight, RespectsRight.postcomp, of_isPullback, of_precomp, postcomp
-/
instance [Q.IsStableUnderBaseChange] [P.HasOfPrecompProperty Q] [P.RespectsRight Q] :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    apply P.of_precomp (W' := Q) _ _ (Q.of_isPullback h hf)
    rw [← h.1.1]
    exact RespectsRight.postcomp _ hf _ hfst

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacks
  signature: C] (P Q
  body: by
  apply DescendsAlong.mk'
  introv hf hfst
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫


中文:
实例 [HasPullbacks
  签名: C] (P Q
  定义体: by
  apply DescendsAlong.mk'
  introv hf hfst
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫


Depends on / 依赖: DescendsAlong, DescendsAlong.mk, MorphismProperty, MorphismProperty.of_pul, condition, congrHom, diagonal, diagonalObjPullbackFstIso, diagonal_iff, hom_ext, introv, of_pul, pullback, pullback.condition, pullback.congrHom, pullback.diagonal, pullback.fst, pullback.hom_ext, pullback.snd, pullbackRightPullbackFstIso
-/
instance [HasPullbacks C] (P Q : MorphismProperty C) [P.DescendsAlong Q] [P.RespectsIso]
    [Q.IsStableUnderBaseChange] :
    DescendsAlong (diagonal P) Q := by
  apply DescendsAlong.mk'
  introv hf hfst
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫
      pullback.diagonal (pullback.fst f g) ≫
      (diagonalObjPullbackFstIso f g).hom := by
    apply pullback.hom_ext
    apply pullback.hom_ext <;> simp [pullback.condition]
    simp [pullback.condition]
  rw [diagonal_iff]
  apply MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) (Q := Q)
      (f := pullback.fst (pullback.snd g g ≫ g) f)
  · exact MorphismProperty.pullback_fst _ _ hf
  · rw [heq]
    iterate 4 rw [cancel_left_of_respectsIso (P := P)]
    rwa [cancel_right_of_respectsIso (P := P)]

/--
lemma `eq_of_isomorphisms_descendsAlong` / 引理 `eq_of_isomorphisms_descendsAlong`

English:
lemma eq_of_isomorphisms_descendsAlong
  statement: [(MorphismProperty.isomorphisms C).DescendsAlong P]
  proof: by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  apply (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback _ _).flip (P.pullback_fst s v hv)
  have : pullback.snd (equalizer.ι f g) (pullback

中文:
引理 eq_of_isomorphisms_descendsAlong
  结论: [(Morphism命题erty.isomorphisms C).DescendsAlong P]
  证明: by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  apply (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback _ _).flip (P.pullback_fst s v hv)
  have : pullback.snd (equalizer.ι f g) (pullback

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Limits, Limits.eq_of_epi_equalizer, MorphismProperty, MorphismProperty.isomorphisms, P.pullback_fst, condition, eq_of_epi_equalizer, equalizer, equalizerPullbackMapIso, isomorphisms, of_hasPullback, of_isPullback_of_descendsAlong, pullback, pullback.condition, pullback.fst, pullback.snd, pullback_fst
-/
lemma eq_of_isomorphisms_descendsAlong [(MorphismProperty.isomorphisms C).DescendsAlong P]
    [P.IsStableUnderBaseChange] [HasEqualizers C]
    [HasPullbacks C] {X Y S T : C} {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s)
    (hg : g ≫ t = s) (v : T ⟶ S) (hv : P v)
    (H :
      pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  apply (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback _ _).flip (P.pullback_fst s v hv)
  have : pullback.snd (equalizer.ι f g) (pullback.fst s v) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq H

set_option backward.isDefEq.respectTransparency false in
/--
lemma `faithful_overPullback_of_isomorphisms_descendAlong` / 引理 `faithful_overPullback_of_isomorphisms_descendAlong`

English:
lemma faithful_overPullback_of_isomorphisms_descendAlong
  proof: by
  refine ⟨fun {X} Y a b hab => ?_⟩
  ext
  apply P.eq_of_isomorphisms_descendsAlong (Over.w a) (Over.w b) f hf
  convert! congr($(hab).left) <;> ext <;> simp

中文:
引理 faithful_overPullback_of_isomorphisms_descendAlong
  证明: by
  refine ⟨fun {X} Y a b hab => ?_⟩
  ext
  apply P.eq_of_isomorphisms_descendsAlong (Over.w a) (Over.w b) f hf
  convert! congr($(hab).left) <;> ext <;> simp

Depends on / 依赖: Over.w, P.eq_of_isomorphisms_descendsAlong, convert, eq_of_isomorphisms_descendsAlong
-/
lemma faithful_overPullback_of_isomorphisms_descendAlong
    [(MorphismProperty.isomorphisms C).DescendsAlong P] [P.IsStableUnderBaseChange]
    [HasPullbacks C] [HasEqualizers C] {S T : C} {f : T ⟶ S} (hf : P f) :
    (Over.pullback f).Faithful := by
  refine ⟨fun {X} Y a b hab => ?_⟩
  ext
  apply P.eq_of_isomorphisms_descendsAlong (Over.w a) (Over.w b) f hf
  convert! congr($(hab).left) <;> ext <;> simp

end DescendsAlong

/--
Definition of `CodescendsAlong` / `CodescendsAlong` 的定义

English:
class CodescendsAlong
  parameters: (P Q : MorphismProperty C)
  axioms and operations (1):
    - of_isPushout({Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}) : IsPushout f g inl inr -> Q f -> P inl -> P g

中文:
类 CodescendsAlong
  参数: (P Q : Morphism命题erty C)
  公理与运算 (1 个):
    - of_isPushout({Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}) : IsPushout f g inl inr -> Q f -> P inl -> P g
-/
class CodescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPushout {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A} :
    IsPushout f g inl inr -> Q f -> P inl -> P g

section CodescendsAlong

variable {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}

/--
lemma `of_isPushout_of_codescendsAlong` / 引理 `of_isPushout_of_codescendsAlong`

English:
lemma of_isPushout_of_codescendsAlong
  statement: [P.CodescendsAlong Q] (h : IsPushout f g inl inr)
  proof: CodescendsAlong.of_isPushout h hf hinl

中文:
引理 of_isPushout_of_codescendsAlong
  结论: [P.CodescendsAlong Q] (h : IsPushout f g inl inr)
  证明: CodescendsAlong.of_isPushout h hf hinl

Depends on / 依赖: CodescendsAlong, CodescendsAlong.of_isPushout, of_isPushout
-/
lemma of_isPushout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr)
    (hf : Q f) (hinl : P inl) : P g :=
  CodescendsAlong.of_isPushout h hf hinl

/--
lemma `iff_of_isPushout` / 引理 `iff_of_isPushout`

English:
lemma iff_of_isPushout
  statement: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q]
  proof: ⟨fun hinl => of_isPushout_of_codescendsAlong h hg hinl, fun hf => P.of_isPushout h hf⟩

中文:
引理 iff_of_isPushout
  结论: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q]
  证明: ⟨fun hinl => of_isPushout_of_codescendsAlong h hg hinl, fun hf => P.of_isPushout h hf⟩

Depends on / 依赖: P.of_isPushout, of_isPushout, of_isPushout_of_codescendsAlong
-/
lemma iff_of_isPushout [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q]
    (h : IsPushout f g inl inr) (hg : Q f) : P inl ↔ P g :=
  ⟨fun hinl => of_isPushout_of_codescendsAlong h hg hinl, fun hf => P.of_isPushout h hf⟩

/--
lemma `of_pushout_inl_of_codescendsAlong` / 引理 `of_pushout_inl_of_codescendsAlong`

English:
lemma of_pushout_inl_of_codescendsAlong
  statement: [P.CodescendsAlong Q] [HasPushout f g] (hf : Q f)
  proof: of_isPushout_of_codescendsAlong (.of_hasPushout f g) hf hinl

中文:
引理 of_pushout_inl_of_codescendsAlong
  结论: [P.CodescendsAlong Q] [HasPushout f g] (hf : Q f)
  证明: of_isPushout_of_codescendsAlong (.of_hasPushout f g) hf hinl

Depends on / 依赖: of_hasPushout, of_isPushout_of_codescendsAlong
-/
lemma of_pushout_inl_of_codescendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hf : Q f)
    (hinl : P (pushout.inl f g)) : P g :=
  of_isPushout_of_codescendsAlong (.of_hasPushout f g) hf hinl

/--
lemma `pushout_inl_iff` / 引理 `pushout_inl_iff`

English:
lemma pushout_inl_iff
  statement: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
  proof: iff_of_isPushout (.of_hasPushout f g) hf

中文:
引理 pushout_inl_iff
  结论: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
  证明: iff_of_isPushout (.of_hasPushout f g) hf

Depends on / 依赖: iff_of_isPushout, of_hasPushout
-/
lemma pushout_inl_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hf : Q f) : P (pushout.inl f g) ↔ P g :=
  iff_of_isPushout (.of_hasPushout f g) hf

/--
lemma `of_pushout_inr_of_descendsAlong` / 引理 `of_pushout_inr_of_descendsAlong`

English:
lemma of_pushout_inr_of_descendsAlong
  statement: [P.CodescendsAlong Q] [HasPushout f g] (hg : Q g)
  proof: of_isPushout_of_codescendsAlong (IsPushout.of_hasPushout f g).flip hg hinr

中文:
引理 of_pushout_inr_of_descendsAlong
  结论: [P.CodescendsAlong Q] [HasPushout f g] (hg : Q g)
  证明: of_isPushout_of_codescendsAlong (IsPushout.of_hasPushout f g).flip hg hinr

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, of_hasPushout, of_isPushout_of_codescendsAlong
-/
lemma of_pushout_inr_of_descendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hg : Q g)
    (hinr : P (pushout.inr f g)) : P f :=
  of_isPushout_of_codescendsAlong (IsPushout.of_hasPushout f g).flip hg hinr

/--
lemma `pushout_inr_iff` / 引理 `pushout_inr_iff`

English:
lemma pushout_inr_iff
  statement: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
  proof: iff_of_isPushout (IsPushout.of_hasPushout f g).flip hg

中文:
引理 pushout_inr_iff
  结论: [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
  证明: iff_of_isPushout (IsPushout.of_hasPushout f g).flip hg

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, iff_of_isPushout, of_hasPushout
-/
lemma pushout_inr_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hg : Q g) : P (pushout.inr f g) ↔ P f :=
  iff_of_isPushout (IsPushout.of_hasPushout f g).flip hg

/--
lemma `CodescendsAlong.of_le` / 引理 `CodescendsAlong.of_le`

English:
lemma CodescendsAlong.of_le
  given: [P.CodescendsAlong Q] (hle : W <= Q)
  statement: P.CodescendsAlong W where
  proof: CodescendsAlong.of_isPushout h (hle _ hg) hinl

中文:
引理 CodescendsAlong.of_le
  条件: [P.CodescendsAlong Q] (hle : W <= Q)
  结论: P.CodescendsAlong W where
  证明: CodescendsAlong.of_isPushout h (hle _ hg) hinl

Depends on / 依赖: CodescendsAlong, CodescendsAlong.of_isPushout, of_isPushout
-/
lemma CodescendsAlong.of_le [P.CodescendsAlong Q] (hle : W <= Q) : P.CodescendsAlong W where
  of_isPushout h hg hinl := CodescendsAlong.of_isPushout h (hle _ hg) hinl

/--
Instance `CodescendsAlong.top` / 实例 `CodescendsAlong.top`

English:
instance CodescendsAlong.top
  signature: : (⊤ : MorphismProperty C).CodescendsAlong Q where
  body: trivial

中文:
实例 CodescendsAlong.top
  签名: : (⊤ : Morphism命题erty C).CodescendsAlong Q where
  定义体: trivial
-/
instance CodescendsAlong.top : (⊤ : MorphismProperty C).CodescendsAlong Q where
  of_isPushout _ _ _ := trivial

/--
Instance `CodescendsAlong.inf` / 实例 `CodescendsAlong.inf`

English:
instance CodescendsAlong.inf
  signature: [P.CodescendsAlong Q] [W.CodescendsAlong Q]
  body: ⟨CodescendsAlong.of_isPushout h hg hfst.1, CodescendsAlong.of_isPushout h hg hfst.2⟩

中文:
实例 CodescendsAlong.inf
  签名: [P.CodescendsAlong Q] [W.CodescendsAlong Q]
  定义体: ⟨CodescendsAlong.of_isPushout h hg hfst.1, CodescendsAlong.of_isPushout h hg hfst.2⟩

Depends on / 依赖: CodescendsAlong, CodescendsAlong.of_isPushout, of_isPushout
-/
instance CodescendsAlong.inf [P.CodescendsAlong Q] [W.CodescendsAlong Q] :
    (P ⊓ W).CodescendsAlong Q where
  of_isPushout h hg hfst :=
    ⟨CodescendsAlong.of_isPushout h hg hfst.1, CodescendsAlong.of_isPushout h hg hfst.2⟩

/--
lemma `CodescendsAlong.mk'` / 引理 `CodescendsAlong.mk'`

English:
lemma CodescendsAlong.mk'
  statement: [P.RespectsIso]
  proof: by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]

中文:
引理 CodescendsAlong.mk'
  结论: [P.RespectsIso]
  证明: by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]

Depends on / 依赖: HasPushout, P.cancel_right_of_respectsIso, cancel_right_of_respectsIso, h.hasPushout, h.inl_isoPushout_inv, h.isoPushout.inv, hasPushout, inl_isoPushout_inv, isoPushout
-/
lemma CodescendsAlong.mk' [P.RespectsIso]
    (H : forall {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} [HasPushout f g], Q f -> P (pushout.inl f g) -> P g) :
    P.CodescendsAlong Q where
  of_isPushout {A X Y Z f g inl inr} h hf hfst := by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsStableUnderCobaseChange]
  signature: [P.HasOfPostcompProperty Q] [P.RespectsLeft Q]
  body: by
    apply P.of_postcomp (W' := Q) g inr (Q.of_isPushout h.flip hf)
    rw [← h.1.1]
    exact RespectsLeft.precomp _ hf _ hinl

中文:
实例 [Q.IsStableUnderCobaseChange]
  签名: [P.HasOfPostcomp命题erty Q] [P.RespectsLeft Q]
  定义体: by
    apply P.of_postcomp (W' := Q) g inr (Q.of_isPushout h.flip hf)
    rw [← h.1.1]
    exact RespectsLeft.precomp _ hf _ hinl

Depends on / 依赖: P.of_postcomp, Q.of_isPushout, RespectsLeft, RespectsLeft.precomp, h.flip, of_isPushout, of_postcomp, precomp
-/
instance [Q.IsStableUnderCobaseChange] [P.HasOfPostcompProperty Q] [P.RespectsLeft Q] :
    P.CodescendsAlong Q where
  of_isPushout {X Y Z A f g inl inr} h hf hinl := by
    apply P.of_postcomp (W' := Q) g inr (Q.of_isPushout h.flip hf)
    rw [← h.1.1]
    exact RespectsLeft.precomp _ hf _ hinl

end CodescendsAlong

end CategoryTheory.MorphismProperty
