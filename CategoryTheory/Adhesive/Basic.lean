/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!

# Adhesive categories

## Main definitions
- `CategoryTheory.IsPushout.IsVanKampen`: A convenience formulation for a pushout being
  a van Kampen colimit.
- `CategoryTheory.Adhesive`: A category is adhesive if it has pushouts and pullbacks along
  monomorphisms, and such pushouts are van Kampen.

## Main Results
- `CategoryTheory.Type.adhesive`: The category of `Type` is adhesive.
- `CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left`: In adhesive categories,
  pushouts along monomorphisms are pullbacks.
- `CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left`: In adhesive categories,
  monomorphisms are stable under pushouts.
- `CategoryTheory.Adhesive.toRegularMonoCategory`: Monomorphisms in adhesive categories are
  regular (this implies that adhesive categories are balanced).
- `CategoryTheory.adhesive_functor`: The category `C ⥤ D` is adhesive if `D`
  has all pullbacks and all pushouts and is adhesive

## References
- https://ncatlab.org/nlab/show/adhesive+category
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/

@[expose] public section


namespace CategoryTheory

open Limits

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

-- This only makes sense when the original diagram is a pushout.
/-- A convenient formulation for a pushout being a van Kampen colimit. For any commutative cube of
which a van Kampen pushout forms the bottom face and the back faces are pullbacks, the front faces
are pullbacks if and only if the top face is a pushout. See `IsPushout.isVanKampen_iff` below. -/
@[nolint unusedArguments]
/--
Definition of `IsPushout.IsVanKampen` / `IsPushout.IsVanKampen` 的定义

English:
definition IsPushout.IsVanKampen
  signature: (_ : IsPushout f g h i)
  body: forall ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (_ : IsPullback f' αW αX f)
    (_ : IsPullback g' αW αY g) (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i)
    (_ : CommSq f' g' h' i'), IsPushout f' g' h

中文:
定义 是推出.IsVanKampen
  签名: (_ : 是推出 f g h i)
  定义体: forall ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (_ : IsPullback f' αW αX f)
    (_ : IsPullback g' αW αY g) (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i)
    (_ : CommSq f' g' h' i'), IsPushout f' g' h

Depends on / 依赖: CommSq, IsPullback, IsPushout
-/
def IsPushout.IsVanKampen (_ : IsPushout f g h i) : Prop :=
  forall ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (_ : IsPullback f' αW αX f)
    (_ : IsPullback g' αW αY g) (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i)
    (_ : CommSq f' g' h' i'), IsPushout f' g' h' i' ↔ IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i

/--
lemma `IsPushout.IsVanKampen.exists_cube_filling` / 引理 `IsPushout.IsVanKampen.exists_cube_filling`

English:
lemma IsPushout.IsVanKampen.exists_cube_filling
  statement: {H : IsPushout f g h i} (H' : H.IsVanKampen)
  proof: by
  let l := hi.lift ((pullback.fst αX f) ≫ h') ((pullback.snd αX f) ≫ g)
    (by simp only [Category.assoc, hh.toCommSq.w, pullback.condition_assoc, ← H.w])
  use (pullback αX f), (pullback.fst αX f), l, (pullback.snd αX f)
  refine ⟨IsPullback.of_hasPullback αX f, ?_, ?_⟩
  · refine IsPullback.of

中文:
引理 是推出.IsVanKampen.存在_cube_filling
  结论: {H : 是推出 f g h i} (H' : H.IsVanKampen)
  证明: by
  let l := hi.lift ((pullback.fst αX f) ≫ h') ((pullback.snd αX f) ≫ g)
    (by simp only [Category.assoc, hh.toCommSq.w, pullback.condition_assoc, ← H.w])
  use (pullback αX f), (pullback.fst αX f), l, (pullback.snd αX f)
  refine ⟨IsPullback.of_hasPullback αX f, ?_, ?_⟩
  · refine IsPullback.of

Depends on / 依赖: Category, Category.assoc, IsPullback, IsPullback.of_hasPullback, IsPullback.of_right, IsPullback.paste_horiz, condition_assoc, hh.toCommSq, hh.toCommSq.w, hi.lift, hi.t, of_hasPullback, of_right, paste_horiz, pullback, pullback.condition_assoc, pullback.fst, pullback.snd, toCommSq
-/
lemma IsPushout.IsVanKampen.exists_cube_filling {H : IsPushout f g h i} (H' : H.IsVanKampen)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'} {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}
    [HasPullback αX f] (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i) :
    exists (W' : C) (f' : W' ⟶ X') (g' : W' ⟶ Y') (αW : W' ⟶ W),
      IsPullback f' αW αX f ∧ IsPullback g' αW αY g ∧ IsPushout f' g' h' i' := by
  let l := hi.lift ((pullback.fst αX f) ≫ h') ((pullback.snd αX f) ≫ g)
    (by simp only [Category.assoc, hh.toCommSq.w, pullback.condition_assoc, ← H.w])
  use (pullback αX f), (pullback.fst αX f), l, (pullback.snd αX f)
  refine ⟨IsPullback.of_hasPullback αX f, ?_, ?_⟩
  · refine IsPullback.of_right' ?_ hi
    rw [← H.w]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) hh
  · refine (H' (pullback.fst αX f) l h' i' (pullback.snd αX f) αX αY αZ
      (IsPullback.of_hasPullback αX f) ?_
        hh.toCommSq hi.toCommSq ⟨by simp only [IsPullback.lift_fst, l]⟩).2 ⟨hh, hi⟩
    · refine IsPullback.of_right' ?_ hi
      rw [← H.w]
      exact IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) hh

/--
theorem `IsPushout.IsVanKampen.flip` / 定理 `IsPushout.IsVanKampen.flip`

English:
theorem IsPushout.IsVanKampen.flip
  given: {H : IsPushout f g h i} (H' : H.IsVanKampen)
  proof: by
  introv W' hf hg hh hi w
  simpa only [IsPushout.flip_iff, IsPullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip

中文:
定理 是推出.IsVanKampen.flip
  条件: {H : 是推出 f g h i} (H' : H.IsVanKampen)
  证明: by
  introv W' hf hg hh hi w
  simpa only [IsPushout.flip_iff, IsPullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip

Depends on / 依赖: IsPullback, IsPullback.flip_iff, IsPushout, IsPushout.flip_iff, and_comm, flip_iff, introv, w.flip
-/
theorem IsPushout.IsVanKampen.flip {H : IsPushout f g h i} (H' : H.IsVanKampen) :
    H.flip.IsVanKampen := by
  introv W' hf hg hh hi w
  simpa only [IsPushout.flip_iff, IsPullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsPushout.isVanKampen_iff` / 定理 `IsPushout.isVanKampen_iff`

English:
theorem IsPushout.isVanKampen_iff
  given: (H : IsPushout f g h i)
  proof: by
  constructor
  · intro H F' c' α fα eα hα
    refine Iff.trans ?_
        ((H (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) (c'.ι.app _) (c'.ι.app _)
          (α.app _) (α.app _) (α.app _) fα (by convert! hα WalkingSpan.Hom.fst)
          (by convert! hα WalkingSpan.Hom.snd) ?_ ?_ ?

中文:
定理 是推出.isVanKampen_iff
  条件: (H : 是推出 f g h i)
  证明: by
  constructor
  · intro H F' c' α fα eα hα
    refine Iff.trans ?_
        ((H (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) (c'.ι.app _) (c'.ι.app _)
          (α.app _) (α.app _) (α.app _) fα (by convert! hα WalkingSpan.Hom.fst)
          (by convert! hα WalkingSpan.Hom.snd) ?_ ?_ ?

Depends on / 依赖: Cocone, Cocone.w, Iff.trans, IsColimit, IsColimit.equivOfNatIsoOfIso, PushoutCocone, PushoutCocone.mk, WalkingSpan, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, WalkingSpan.left, WalkingSpan.right, convert, diagramIsoSpan, equivOfNatIsoOfIso
-/
theorem IsPushout.isVanKampen_iff (H : IsPushout f g h i) :
    H.IsVanKampen ↔ IsVanKampenColimit (PushoutCocone.mk h i H.w) := by
  constructor
  · intro H F' c' α fα eα hα
    refine Iff.trans ?_
        ((H (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) (c'.ι.app _) (c'.ι.app _)
          (α.app _) (α.app _) (α.app _) fα (by convert! hα WalkingSpan.Hom.fst)
          (by convert! hα WalkingSpan.Hom.snd) ?_ ?_ ?_).trans ?_)
    · have : F'.map WalkingSpan.Hom.fst ≫ c'.ι.app WalkingSpan.left =
          F'.map WalkingSpan.Hom.snd ≫ c'.ι.app WalkingSpan.right := by
        simp only [Cocone.w]
      rw [(IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') c' (PushoutCocone.mk _ _ this)
            _).nonempty_congr]
      · exact ⟨fun h => ⟨⟨this⟩, h⟩, fun h => h.2⟩
      · refine Cocone.ext (Iso.refl c'.pt) ?_
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [c'.w, Category.id_comp, Category.comp_id]
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨by simp⟩
    constructor
    · rintro ⟨h₁, h₂⟩ (_ | _ | _)
      · rw [← c'.w WalkingSpan.Hom.fst]; exact (hα WalkingSpan.Hom.fst).paste_horiz h₁
      exacts [h₁, h₂]
    · intro h; exact ⟨h _, h _⟩
  · introv H W' hf hg hh hi w
    refine
      Iff.trans ?_ ((H w.cocone ⟨by rintro (_ | _ | _); exacts [αW, αX, αY], ?_⟩ αZ ?_ ?_).trans ?_)
    rotate_left
    · rintro i _ (_ | _ | _)
      · dsimp; simp only [Functor.map_id, Category.comp_id, Category.id_comp]
      exacts [hf.w, hg.w]
    · ext (_ | _ | _)
      · simp [hh.w, hf.w_assoc]
      exacts [hh.w.symm, hi.w.symm]
    · rintro i _ (_ | _ | _)
      · dsimp; simp_rw [Functor.map_id]
        exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
      exacts [hf, hg]
    · constructor
      · intro h; exact ⟨h WalkingCospan.left, h WalkingCospan.right⟩
      · rintro ⟨h₁, h₂⟩ (_ | _ | _)
        · dsimp; rw [PushoutCocone.condition_zero]; exact hf.paste_horiz h₁
        exacts [h₁, h₂]
    · exact ⟨fun h => h.2, fun h => ⟨w, h⟩⟩

/--
theorem `IsPushout.isVanKampen_iff'` / 定理 `IsPushout.isVanKampen_iff'`

English:
theorem IsPushout.isVanKampen_iff'
  given: {H : IsPushout f g h i}
  proof: by
  constructor
  · intro H' X' Y' Z' h' i' αX αY αZ sq_h sq_i _
    constructor
    · intro ⟨hh, hi⟩
      exact H'.exists_cube_filling hh hi
    · intro ⟨W', f', g', αW, hf, hg, H''⟩
      rwa [← H' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i H''.toCommSq]
  · intro H' W' X' Y' Z' f' g' h' i' αW αX α

中文:
定理 是推出.isVanKampen_iff'
  条件: {H : 是推出 f g h i}
  证明: by
  constructor
  · intro H' X' Y' Z' h' i' αX αY αZ sq_h sq_i _
    constructor
    · intro ⟨hh, hi⟩
      exact H'.exists_cube_filling hh hi
    · intro ⟨W', f', g', αW, hf, hg, H''⟩
      rwa [← H' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i H''.toCommSq]
  · intro H' W' X' Y' Z' f' g' h' i' αW αX α

Depends on / 依赖: HasPullback, exists_cube_filling, hasPullback, hf.hasPullback, sq_h, sq_i, toCommSq
-/
theorem IsPushout.isVanKampen_iff' {H : IsPushout f g h i} :
    H.IsVanKampen ↔ forall ⦃X' Y' Z' : C⦄ (h' : X' ⟶ Z') (i' : Y' ⟶ Z')
      (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z)
      (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i) [HasPullback αX f],
      IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i ↔
        exists (W' : C) (f' : W' ⟶ X') (g' : W' ⟶ Y') (αW : W' ⟶ W),
      IsPullback f' αW αX f ∧ IsPullback g' αW αY g ∧ IsPushout f' g' h' i' := by
  constructor
  · intro H' X' Y' Z' h' i' αX αY αZ sq_h sq_i _
    constructor
    · intro ⟨hh, hi⟩
      exact H'.exists_cube_filling hh hi
    · intro ⟨W', f', g', αW, hf, hg, H''⟩
      rwa [← H' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i H''.toCommSq]
  · intro H' W' X' Y' Z' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i cs
    let : HasPullback αX f := hf.hasPullback
    constructor
    · intro H''
      rw [H' h' i' αX αY αZ sq_h sq_i]
      refine ⟨W', f', g', αW, hf, hg, H''⟩
    · intro ⟨hh, hi⟩
      obtain ⟨W'', f'', g'', αW', hf', hg', hP⟩ := (H' h' i' αX αY αZ sq_h sq_i).1 ⟨hh, hi⟩
      refine hP.of_iso (IsPullback.isoIsPullback _ _ hf' hf)
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
      · apply hi.hom_ext
        · simp [← cs.w, hP.w]
        · simp [hg.w, hg'.w]

/--
lemma `IsPushout.isVanKampen_isPullback_isPullback_hom_ext` / 引理 `IsPushout.isVanKampen_isPullback_isPullback_hom_ext`

English:
lemma IsPushout.isVanKampen_isPullback_isPullback_hom_ext
  proof: by
  obtain ⟨W', f', g', αW, _, _, H''⟩ := H'.exists_cube_filling hh hi
  exact H''.hom_ext h'_w i'_w

中文:
引理 是推出.isVanKampen_isPullback_isPullback_hom_ext
  证明: by
  obtain ⟨W', f', g', αW, _, _, H''⟩ := H'.exists_cube_filling hh hi
  exact H''.hom_ext h'_w i'_w

Depends on / 依赖: exists_cube_filling, hom_ext
-/
lemma IsPushout.isVanKampen_isPullback_isPullback_hom_ext
    {H : IsPushout f g h i} (H' : H.IsVanKampen)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} [HasPullback αX f] {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z} {W : C} {f₁ f₂ : Z' ⟶ W}
    (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i)
    (h'_w : h' ≫ f₁ = h' ≫ f₂) (i'_w : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ := by
  obtain ⟨W', f', g', αW, _, _, H''⟩ := H'.exists_cube_filling hh hi
  exact H''.hom_ext h'_w i'_w

set_option backward.isDefEq.respectTransparency false in
/--
theorem `is_coprod_iff_isPushout` / 定理 `is_coprod_iff_isPushout`

English:
theorem is_coprod_iff_isPushout
  statement: {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y}
  proof: by
  constructor
  · rintro ⟨h⟩
    refine ⟨H, ⟨Limits.PushoutCocone.isColimitAux' _ ?_⟩⟩
    intro s
    dsimp
    refine ⟨BinaryCofan.IsColimit.desc h (c.inr ≫ s.inr) s.inl,
        BinaryCofan.IsColimit.inr_desc h _ _, ?_, ?_⟩
    · apply BinaryCofan.IsColimit.hom_ext hc
      · rw [← H.w_assoc];

中文:
定理 is_coprod_iff_isPushout
  结论: {X E Y YE : C} (c : BinaryCofan X E) (hc : 是余极限 c) {f : X ⟶ Y}
  证明: by
  constructor
  · rintro ⟨h⟩
    refine ⟨H, ⟨Limits.PushoutCocone.isColimitAux' _ ?_⟩⟩
    intro s
    dsimp
    refine ⟨BinaryCofan.IsColimit.desc h (c.inr ≫ s.inr) s.inl,
        BinaryCofan.IsColimit.inr_desc h _ _, ?_, ?_⟩
    · apply BinaryCofan.IsColimit.hom_ext hc
      · rw [← H.w_assoc];

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.hom_ext, BinaryCofan.IsColimit.inr_desc, Category, Category.assoc, H.w_assoc, IsColimit, Limits, Limits.PushoutCocone.isColimitAux, PushoutCocone, WalkingPair, WalkingPair.left, WalkingPair.right, c.inr, condition, eq_comm, h.fac, hom_ext, inr_desc
-/
theorem is_coprod_iff_isPushout {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y}
    {iY : Y ⟶ YE} {fE : c.pt ⟶ YE} (H : CommSq f c.inl iY fE) :
    Nonempty (IsColimit (BinaryCofan.mk (c.inr ≫ fE) iY)) ↔ IsPushout f c.inl iY fE := by
  constructor
  · rintro ⟨h⟩
    refine ⟨H, ⟨Limits.PushoutCocone.isColimitAux' _ ?_⟩⟩
    intro s
    dsimp
    refine ⟨BinaryCofan.IsColimit.desc h (c.inr ≫ s.inr) s.inl,
        BinaryCofan.IsColimit.inr_desc h _ _, ?_, ?_⟩
    · apply BinaryCofan.IsColimit.hom_ext hc
      · rw [← H.w_assoc]; erw [h.fac _ ⟨WalkingPair.right⟩]; exact s.condition
      · rw [← Category.assoc]; exact h.fac _ ⟨WalkingPair.left⟩
    · intro m e₁ e₂
      apply BinaryCofan.IsColimit.hom_ext h
      · dsimp
        rw [Category.assoc]; rw [e₂]; rw [eq_comm]; exact h.fac _ ⟨WalkingPair.left⟩
      · refine e₁.trans (Eq.symm ?_); exact h.fac _ _
  · refine fun H => ⟨?_⟩
    fapply Limits.BinaryCofan.isColimitMk
    · exact fun s => H.isColimit.desc (PushoutCocone.mk s.inr _ <|
        (hc.fac (BinaryCofan.mk (f ≫ s.inr) s.inl) ⟨WalkingPair.left⟩).symm)
    · intro s
      rw [Category.assoc]
      erw [H.isColimit.fac _ WalkingSpan.right]
      erw [hc.fac]
      rfl
    · intro s; exact H.isColimit.fac _ WalkingSpan.left
    · intro s m e₁ e₂
      apply PushoutCocone.IsColimit.hom_ext H.isColimit
      · symm; exact (H.isColimit.fac _ WalkingSpan.left).trans e₂.symm
      · rw [H.isColimit.fac _ WalkingSpan.right]
        apply BinaryCofan.IsColimit.hom_ext hc
        · erw [hc.fac]
          erw [← H.w_assoc]
          rw [e₂]
          rfl
        · refine ((Category.assoc _ _ _).symm.trans e₁).trans ?_; symm; exact hc.fac _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsPushout.isVanKampen_inl` / 定理 `IsPushout.isVanKampen_inl`

English:
theorem IsPushout.isVanKampen_inl
  statement: {W E X Z : C} (c : BinaryCofan W E) [FinitaryExtensive C]
  proof: by
  obtain ⟨hc₁⟩ := (is_coprod_iff_isPushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
    (BinaryCofan.mk _ (pullback.fst _ _)) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, IsPullback.of_hasPullback α

中文:
定理 是推出.isVanKampen_inl
  结论: {W E X Z : C} (c : BinaryCofan W E) [有限广延 C]
  证明: by
  obtain ⟨hc₁⟩ := (is_coprod_iff_isPushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
    (BinaryCofan.mk _ (pullback.fst _ _)) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, IsPullback.of_hasPullback α

Depends on / 依赖: BinaryCofan, BinaryCofan.isVanKampen_iff, BinaryCofan.mk, FinitaryExtensive, FinitaryExtensive.vanKampen, IsPullback, IsPullback.of_hasPullback, c.inr, condition, hg.w.symm, hh.w.symm, introv, isVanKampen_iff, is_coprod_iff_isPushout, of_hasPullback, pullback, pullback.condition.symm, pullback.fst, pullback.snd, symm.trans
-/
theorem IsPushout.isVanKampen_inl {W E X Z : C} (c : BinaryCofan W E) [FinitaryExtensive C]
    [HasPullbacks C] (hc : IsColimit c) (f : W ⟶ X) (h : X ⟶ Z) (i : c.pt ⟶ Z)
    (H : IsPushout f c.inl h i) : H.IsVanKampen := by
  obtain ⟨hc₁⟩ := (is_coprod_iff_isPushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
    (BinaryCofan.mk _ (pullback.fst _ _)) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, IsPullback.of_hasPullback αY c.inr⟩
  refine (is_coprod_iff_isPushout _ hc₂ w).symm.trans ?_
  refine ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hc₁)
    (BinaryCofan.mk _ _) (pullback.snd _ _) _ _ ?_ hh.w.symm).trans ?_
  · dsimp; rw [← pullback.condition_assoc, Category.assoc, hi.w]
  constructor
  · rintro ⟨hc₃, hc₄⟩
    refine ⟨hc₄, ?_⟩
    let Y'' := pullback αZ i
    let cmp : Y' ⟶ Y'' := pullback.lift i' αY hi.w
    have e₁ : (g' ≫ cmp) ≫ pullback.snd _ _ = αW ≫ c.inl := by
      rw [Category.assoc]; rw [pullback.lift_snd]; rw [hg.w]
    have e₂ : (pullback.fst _ _ ≫ cmp : pullback αY c.inr ⟶ _) ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ c.inr := by
      rw [Category.assoc]; rw [pullback.lift_snd]; rw [pullback.condition]
    obtain ⟨hc₄⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
      (BinaryCofan.mk _ _) αW _ _ e₁.symm e₂.symm).mpr <| by
        constructor
        · apply IsPullback.of_right _ e₁ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc]; rw [pullback.lift_fst]; rw [← H.w]; rw [← w.w]; exact hf.paste_horiz hc₄
        · apply IsPullback.of_right _ e₂ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc]; rw [pullback.lift_fst]; exact hc₃
    rw [← Category.id_comp αZ]; rw [← show cmp ≫ pullback.snd _ _ = αY from pullback.lift_snd _ _ _]
    apply IsPullback.paste_vert _ (IsPullback.of_hasPullback αZ i)
    have : cmp = (hc₂.coconePointUniqueUpToIso hc₄).hom := by
      apply BinaryCofan.IsColimit.hom_ext hc₂
      exacts [(hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.left⟩).symm,
        (hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.right⟩).symm]
    rw [this]
    exact IsPullback.of_vert_isIso ⟨by rw [← this, Category.comp_id, pullback.lift_fst]⟩
  · rintro ⟨hc₃, hc₄⟩
    exact ⟨(IsPullback.of_hasPullback αY c.inr).paste_horiz hc₄, hc₃⟩

/--
theorem `IsPushout.IsVanKampen.isPullback_of_mono_left` / 定理 `IsPushout.IsVanKampen.isPullback_of_mono_left`

English:
theorem IsPushout.IsVanKampen.isPullback_of_mono_left
  statement: [Mono f] {H : IsPushout f g h i}
  proof: ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
      (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
    (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip

中文:
定理 是推出.IsVanKampen.isPullback_of_mono_left
  结论: [单态射 f] {H : 是推出 f g h i}
  证明: ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
      (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
    (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip

Depends on / 依赖: IsKernelPair, IsKernelPair.id_of_mono, IsPullback, IsPullback.of_vert_isIso, IsPushout, IsPushout.of_horiz_isIso, id_of_mono, of_horiz_isIso, of_vert_isIso
-/
theorem IsPushout.IsVanKampen.isPullback_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
      (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
    (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip

/--
theorem `IsPushout.IsVanKampen.isPullback_of_mono_right` / 定理 `IsPushout.IsVanKampen.isPullback_of_mono_right`

English:
theorem IsPushout.IsVanKampen.isPullback_of_mono_right
  statement: [Mono g] {H : IsPushout f g h i}
  proof: ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
      (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
    (IsPushout.of_vert_isIso ⟨by simp⟩)).2

中文:
定理 是推出.IsVanKampen.isPullback_of_mono_right
  结论: [单态射 g] {H : 是推出 f g h i}
  证明: ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
      (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
    (IsPushout.of_vert_isIso ⟨by simp⟩)).2

Depends on / 依赖: IsKernelPair, IsKernelPair.id_of_mono, IsPullback, IsPullback.of_vert_isIso, IsPushout, IsPushout.of_vert_isIso, id_of_mono, of_vert_isIso
-/
theorem IsPushout.IsVanKampen.isPullback_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
      (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
    (IsPushout.of_vert_isIso ⟨by simp⟩)).2

/--
theorem `IsPushout.IsVanKampen.mono_of_mono_left` / 定理 `IsPushout.IsVanKampen.mono_of_mono_left`

English:
theorem IsPushout.IsVanKampen.mono_of_mono_left
  statement: [Mono f] {H : IsPushout f g h i}
  proof: IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
        (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
      (IsPushout.of_horiz_isIso ⟨by simp⟩)).2

中文:
定理 是推出.IsVanKampen.mono_of_mono_left
  结论: [单态射 f] {H : 是推出 f g h i}
  证明: IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
        (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
      (IsPushout.of_horiz_isIso ⟨by simp⟩)).2

Depends on / 依赖: IsKernelPair, IsKernelPair.id_of_mono, IsKernelPair.mono_of_isIso_fst, IsPullback, IsPullback.of_vert_isIso, IsPushout, IsPushout.of_horiz_isIso, id_of_mono, mono_of_isIso_fst, of_horiz_isIso, of_vert_isIso
-/
theorem IsPushout.IsVanKampen.mono_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono i :=
  IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
        (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
      (IsPushout.of_horiz_isIso ⟨by simp⟩)).2

/--
theorem `IsPushout.IsVanKampen.mono_of_mono_right` / 定理 `IsPushout.IsVanKampen.mono_of_mono_right`

English:
theorem IsPushout.IsVanKampen.mono_of_mono_right
  statement: [Mono g] {H : IsPushout f g h i}
  proof: IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
        (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).1

中文:
定理 是推出.IsVanKampen.mono_of_mono_right
  结论: [单态射 g] {H : 是推出 f g h i}
  证明: IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
        (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).1

Depends on / 依赖: IsKernelPair, IsKernelPair.id_of_mono, IsKernelPair.mono_of_isIso_fst, IsPullback, IsPullback.of_vert_isIso, IsPushout, IsPushout.of_vert_isIso, id_of_mono, mono_of_isIso_fst, of_vert_isIso
-/
theorem IsPushout.IsVanKampen.mono_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono h :=
  IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
        (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).1

/--
Definition of `Adhesive` / `Adhesive` 的定义

English:
class Adhesive
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (3):
    - [hasPullback_of_mono_left : forall {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
    - [hasPushout_of_mono_left : forall {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    - van_kampen : forall {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [Mono f] (H : IsPushout f g h i), H.IsVanKampen

中文:
类 Adhesive
  参数: (C : 类型u) [范畴.{v} C]
  公理与运算 (3 个):
    - [hasPullback_of_mono_left : 对任意 {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [单态射 f], HasPullback f g]
    - [hasPushout_of_mono_left : 对任意 {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [单态射 f], HasPushout f g]
    - van_kampen : 对任意 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [单态射 f] (H : 是推出 f g h i), H.IsVanKampen
-/
class Adhesive (C : Type u) [Category.{v} C] : Prop where
  [hasPullback_of_mono_left : forall {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
  [hasPushout_of_mono_left : forall {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
  van_kampen : forall {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [Mono f]
    (H : IsPushout f g h i), H.IsVanKampen

attribute [instance] Adhesive.hasPullback_of_mono_left Adhesive.hasPushout_of_mono_left

/--
theorem `Adhesive.van_kampen'` / 定理 `Adhesive.van_kampen'`

English:
theorem Adhesive.van_kampen'
  given: [Adhesive C] [Mono g] (H : IsPushout f g h i)
  statement: H.IsVanKampen
  proof: (Adhesive.van_kampen H.flip).flip

中文:
定理 Adhesive.van_kampen'
  条件: [Adhesive C] [单态射 g] (H : 是推出 f g h i)
  结论: H.IsVanKampen
  证明: (Adhesive.van_kampen H.flip).flip

Depends on / 依赖: Adhesive, Adhesive.van_kampen, H.flip, van_kampen
-/
theorem Adhesive.van_kampen' [Adhesive C] [Mono g] (H : IsPushout f g h i) : H.IsVanKampen :=
  (Adhesive.van_kampen H.flip).flip

/--
theorem `Adhesive.isPullback_of_isPushout_of_mono_left` / 定理 `Adhesive.isPullback_of_isPushout_of_mono_left`

English:
theorem Adhesive.isPullback_of_isPushout_of_mono_left
  statement: [Adhesive C] (H : IsPushout f g h i)
  proof: (Adhesive.van_kampen H).isPullback_of_mono_left

中文:
定理 Adhesive.isPullback_of_isPushout_of_mono_left
  结论: [Adhesive C] (H : 是推出 f g h i)
  证明: (Adhesive.van_kampen H).isPullback_of_mono_left

Depends on / 依赖: Adhesive, Adhesive.van_kampen, isPullback_of_mono_left, van_kampen
-/
theorem Adhesive.isPullback_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i)
    [Mono f] : IsPullback f g h i :=
  (Adhesive.van_kampen H).isPullback_of_mono_left

/--
theorem `Adhesive.isPullback_of_isPushout_of_mono_right` / 定理 `Adhesive.isPullback_of_isPushout_of_mono_right`

English:
theorem Adhesive.isPullback_of_isPushout_of_mono_right
  statement: [Adhesive C] (H : IsPushout f g h i)
  proof: (Adhesive.van_kampen' H).isPullback_of_mono_right

中文:
定理 Adhesive.isPullback_of_isPushout_of_mono_right
  结论: [Adhesive C] (H : 是推出 f g h i)
  证明: (Adhesive.van_kampen' H).isPullback_of_mono_right

Depends on / 依赖: Adhesive, Adhesive.van_kampen, isPullback_of_mono_right, van_kampen
-/
theorem Adhesive.isPullback_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i)
    [Mono g] : IsPullback f g h i :=
  (Adhesive.van_kampen' H).isPullback_of_mono_right

/--
theorem `Adhesive.mono_of_isPushout_of_mono_left` / 定理 `Adhesive.mono_of_isPushout_of_mono_left`

English:
theorem Adhesive.mono_of_isPushout_of_mono_left
  given: [Adhesive C] (H : IsPushout f g h i) [Mono f]
  proof: (Adhesive.van_kampen H).mono_of_mono_left

中文:
定理 Adhesive.mono_of_isPushout_of_mono_left
  条件: [Adhesive C] (H : 是推出 f g h i) [单态射 f]
  证明: (Adhesive.van_kampen H).mono_of_mono_left

Depends on / 依赖: Adhesive, Adhesive.van_kampen, mono_of_mono_left, van_kampen
-/
theorem Adhesive.mono_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i) [Mono f] :
    Mono i :=
  (Adhesive.van_kampen H).mono_of_mono_left

/--
theorem `Adhesive.mono_of_isPushout_of_mono_right` / 定理 `Adhesive.mono_of_isPushout_of_mono_right`

English:
theorem Adhesive.mono_of_isPushout_of_mono_right
  given: [Adhesive C] (H : IsPushout f g h i) [Mono g]
  proof: (Adhesive.van_kampen' H).mono_of_mono_right

中文:
定理 Adhesive.mono_of_isPushout_of_mono_right
  条件: [Adhesive C] (H : 是推出 f g h i) [单态射 g]
  证明: (Adhesive.van_kampen' H).mono_of_mono_right

Depends on / 依赖: Adhesive, Adhesive.van_kampen, mono_of_mono_right, van_kampen
-/
theorem Adhesive.mono_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i) [Mono g] :
    Mono h :=
  (Adhesive.van_kampen' H).mono_of_mono_right

attribute [local instance] Limits.hasPullback_symmetry in
/--
lemma `Adhesive.isPushout_isPullback_isPullback_hom_ext` / 引理 `Adhesive.isPushout_isPullback_isPullback_hom_ext`

English:
lemma Adhesive.isPushout_isPullback_isPullback_hom_ext
  statement: [Adhesive C] [Mono f] (H : IsPushout f g h i)
  proof: IsPushout.isVanKampen_isPullback_isPullback_hom_ext (Adhesive.van_kampen H) hh hi h'_w i'_w

中文:
引理 Adhesive.isPushout_isPullback_isPullback_hom_ext
  结论: [Adhesive C] [单态射 f] (H : 是推出 f g h i)
  证明: IsPushout.isVanKampen_isPullback_isPullback_hom_ext (Adhesive.van_kampen H) hh hi h'_w i'_w

Depends on / 依赖: Adhesive, Adhesive.van_kampen, IsPushout, IsPushout.isVanKampen_isPullback_isPullback_hom_ext, isVanKampen_isPullback_isPullback_hom_ext, van_kampen
-/
lemma Adhesive.isPushout_isPullback_isPullback_hom_ext [Adhesive C] [Mono f] (H : IsPushout f g h i)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}
    {W : C} {f₁ f₂ : Z' ⟶ W}
    (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i)
    (h'_w : h' ≫ f₁ = h' ≫ f₂) (i'_w : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ :=
  IsPushout.isVanKampen_isPullback_isPullback_hom_ext (Adhesive.van_kampen H) hh hi h'_w i'_w

attribute [local instance] Limits.hasPullback_symmetry in
open IsPullback IsPushout pullback pushout in
/--
Instance `Adhesive.desc_mono_of_mono` / 实例 `Adhesive.desc_mono_of_mono`

English:
instance Adhesive.desc_mono_of_mono
  signature: [Adhesive C] {Z A B : C}
  body: by
    /- First, take the pullback of `a` and `b` and then form the pushout of the projection maps:
     `pullback a b` -> `B`
          | |
          | `v`
          | |
          v v
         `A` ---`u`---> C -/
    let u := pushout.inl (pullback.fst a b) (pullback.snd a b)
    let v := pushout.in

中文:
实例 Adhesive.desc_mono_of_mono
  签名: [Adhesive C] {Z A B : C}
  定义体: by
    /- First, take the pullback of `a` and `b` and then form the pushout of the projection maps:
     `pullback a b` -> `B`
          | |
          | `v`
          | |
          v v
         `A` ---`u`---> C -/
    let u := pushout.inl (pullback.fst a b) (pullback.snd a b)
    let v := pushout.in
-/
instance Adhesive.desc_mono_of_mono [Adhesive C] {Z A B : C}
    {a : A ⟶ Z} {b : B ⟶ Z} [Mono a] [Mono b] :
    Mono (pushout.desc a b pullback.condition) where
  right_cancellation {K} f g w := by
    /- First, take the pullback of `a` and `b` and then form the pushout of the projection maps:
     `pullback a b` -> `B`
          | |
          | `v`
          | |
          v v
         `A` ---`u`---> C -/
    let u := pushout.inl (pullback.fst a b) (pullback.snd a b)
    let v := pushout.inr (pullback.fst a b) (pullback.snd a b)
    let : Mono u :=
      mono_of_isPushout_of_mono_right (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    let : Mono v :=
      mono_of_isPushout_of_mono_left (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    /- Then form the following pullbacks:
     L₁ --`l₁`-> K <--`l₂`-- L₂
     | | |
    `f₁` `f` `f₂`
     | | |
     v v v
    `A` --`u`--> C <--`v`-- `B`

     M₁ --`m₁`-> K <--`m₂`-- M₂
     | | |
    `g₁` `g` `g₂`
     | | |
     v v v
    `A` --`u`--> C <--`v`-- `B` -/
    let sq_f_u := of_hasPullback f u
    let sq_f_v := of_hasPullback f v
    let sq_g_u := of_hasPullback g u
    let sq_g_v := of_hasPullback g v
    /- Finally, form the following pullbacks:
     N₁₁ --m₁₁-> M₁ <--m₁₂-- N₁₂
     | | |
    l₁₁ `m₁` l₁₂
     | | |
     v v v
    L₁ --`l₁`--> K <--`l₂`-- L₂
     ^ ^ ^
     | | |
    l₂₁ `m₂` l₂₂
     | | |
    N₂₁ --m₂₁--> M₂ <--m₂₂-- N₂₂
    -/
    let l₁ := pullback.fst f u
    let f₁ := pullback.snd f u
    let l₂ := pullback.fst f v
    let f₂ := pullback.snd f v
    let m₁ := pullback.fst g u
    let g₁ := pullback.snd g u
    let m₂ := pullback.fst g v
    let g₂ := pullback.snd g v
    obtain ⟨_, f', _, _, p₁, _, h₁⟩ :=
      (van_kampen (of_hasPushout _ _)).exists_cube_filling sq_f_u sq_f_v
    let : Mono f' := by
      rw [← p₁.isoPullback_hom_fst]
      infer_instance
    /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `f = g` to `m₁ ≫ f = m₁ ≫ g`
      and `m₂ ≫ f = m₂ ≫ g`. -/
    apply isPushout_isPullback_isPullback_hom_ext (of_hasPushout _ _) sq_g_u sq_g_v
    · let sq₁₁ := of_hasPullback m₁ l₁
      let sq₁₂ := of_hasPullback m₁ l₂
      /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `m₁ ≫ f = m₁ ≫ g` to
        `m₁₁ ≫ m₁ ≫ f = m₁₁ ≫ m₁ ≫ g` and `m₁₂ ≫ m₁ ≫ f = m₁₂ ≫ m₁ ≫ g`. -/
      apply isPushout_isPullback_isPullback_hom_ext h₁ sq₁₁ sq₁₂
      · rw [pullback.condition_assoc, sq_f_u.w, sq_g_u.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ u
        let : Mono (u ≫ pushout.desc a b pullback.condition) := by rwa [pushout.inl_desc]
        rw [← cancel_mono (u ≫ pushout.desc a b pullback.condition)]; rw [Category.assoc]; rw [← sq_f_u.w_assoc]; rw [w]; rw [← pullback.condition_assoc]; rw [Category.assoc]; rw [← sq_g_u.w_assoc]
      · have : (pullback.fst m₁ l₂ ≫ g₁) ≫ a = (pullback.snd m₁ l₂ ≫ f₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition]; rw [Category.assoc]; rw [← sq_g_u.w_assoc]; rw [sq₁₂.w_assoc]; rw [← w]; rw [Category.assoc]; rw [pullback.condition_assoc]; rw [pushout.inr_desc]
        rw [sq₁₂.w_assoc]; rw [sq_f_v.w]; rw [← Category.assoc]; rw [← pullback.lift_snd_assoc _ _ this]; rw [← pushout.condition]; rw [pullback.lift_fst_assoc _ _ this]; rw [Category.assoc]; rw [sq_g_u.w]
    · let sq₂₁ := of_hasPullback m₂ l₁
      let sq₂₂ := of_hasPullback m₂ l₂
      /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `m₂ ≫ f = m₂ ≫ g` to
        `m₂₁ ≫ m₂ ≫ f = m₂₁ ≫ m₂ ≫ g` and `m₂₂ ≫ m₂ ≫ f = m₂₂ ≫ m₂ ≫ g`. -/
      apply isPushout_isPullback_isPullback_hom_ext h₁ sq₂₁ sq₂₂
      · have : (pullback.snd m₂ l₁ ≫ f₁) ≫ a = (pullback.fst m₂ l₁ ≫ g₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition]; rw [Category.assoc]; rw [← sq_f_u.w_assoc]; rw [w]; rw [← sq₂₁.w_assoc]; rw [Category.assoc]; rw [sq_g_v.w_assoc]; rw [pushout.inr_desc]
        rw [sq₂₁.w_assoc]; rw [sq_f_u.w]; rw [← Category.assoc]; rw [← pullback.lift_fst_assoc _ _ this]; rw [pushout.condition]; rw [pullback.lift_snd_assoc _ _ this]; rw [sq_g_v.w]; rw [Category.assoc]
      · rw [sq₂₂.w_assoc, sq_f_v.w, sq_g_v.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ v
        let : Mono (v ≫ pushout.desc a b pullback.condition) := by rwa [pushout.inr_desc]
        rw [← cancel_mono (v ≫ pushout.desc a b pullback.condition)]; rw [Category.assoc]; rw [← sq_f_v.w_assoc]; rw [w]; rw [← pullback.condition_assoc]; rw [Category.assoc]; rw [← sq_g_v.w_assoc]

/--
Instance `Type.adhesive` / 实例 `Type.adhesive`

English:
instance Type.adhesive
  signature: : Adhesive (Type u)
  body: ⟨fun {_ _ _ _ f _ _ _ _} H =>
    (IsPushout.isVanKampen_inl _ (Types.isCoprodOfMono f) _ _ _ H.flip).flip⟩

中文:
实例 类型.adhesive
  签名: : Adhesive (类型u)
  定义体: ⟨fun {_ _ _ _ f _ _ _ _} H =>
    (IsPushout.isVanKampen_inl _ (Types.isCoprodOfMono f) _ _ _ H.flip).flip⟩

Depends on / 依赖: H.flip, IsPushout, IsPushout.isVanKampen_inl, Types.isCoprodOfMono, isCoprodOfMono, isVanKampen_inl
-/
instance Type.adhesive : Adhesive (Type u) :=
  ⟨fun {_ _ _ _ f _ _ _ _} H =>
    (IsPushout.isVanKampen_inl _ (Types.isCoprodOfMono f) _ _ _ H.flip).flip⟩

noncomputable instance (priority := 100) Adhesive.toRegularMonoCategory [Adhesive C] :
    IsRegularMonoCategory C :=
  ⟨fun f _ => ⟨⟨{
      Z := pushout f f
      left := pushout.inl _ _
      right := pushout.inr _ _
      w := pushout.condition
      isLimit := (Adhesive.isPullback_of_isPushout_of_mono_left
        (IsPushout.of_hasPushout f f)).isLimitFork }⟩⟩⟩

-- This then implies that adhesive categories are balanced
example [Adhesive C] : Balanced C :=
  inferInstance

section functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

/--
Instance `adhesive_functor` / 实例 `adhesive_functor`

English:
instance adhesive_functor
  signature: [Adhesive C] [HasPullbacks C] [HasPushouts C]
  body: by
  constructor
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  apply isVanKampenColimit_of_evaluation
  intro x
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isV

中文:
实例 adhesive_functor
  签名: [Adhesive C] [有Pullbacks C] [有Pushouts C]
  定义体: by
  constructor
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  apply isVanKampenColimit_of_evaluation
  intro x
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isV

Depends on / 依赖: Adhesive, Adhesive.van_kampen, H.map, IsPushout, IsPushout.isVanKampen_iff, IsVanKampenColimit, IsVanKampenColimit.of_iso, IsVanKampenColimit.precompose_isIso_iff, PushoutCocone, PushoutCocone.isoMk, diagramIsoSpan, evaluation, isVanKampenColimit_of_evaluation, isVanKampen_iff, of_iso, precompose_isIso_iff, van_kampen
-/
instance adhesive_functor [Adhesive C] [HasPullbacks C] [HasPushouts C] :
    Adhesive (D ⥤ C) := by
  constructor
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  apply isVanKampenColimit_of_evaluation
  intro x
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map ((evaluation _ _).obj x))).mp ?_
  apply Adhesive.van_kampen

/--
theorem `adhesive_of_preserves_and_reflects` / 定理 `adhesive_of_preserves_and_reflects`

English:
theorem adhesive_of_preserves_and_reflects
  statement: (F : C ⥤ D) [Adhesive D]
  proof: by
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  refine IsVanKampenColimit.of_mapCocone F ?_
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColi

中文:
定理 adhesive_of_preserves_and_reflects
  结论: (F : C ⥤ D) [Adhesive D]
  证明: by
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  refine IsVanKampenColimit.of_mapCocone F ?_
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColi

Depends on / 依赖: Adhesive, Adhesive.mk, Adhesive.van_kampen, H.map, IsPushout, IsPushout.isVanKampen_iff, IsVanKampenColimit, IsVanKampenColimit.of_iso, IsVanKampenColimit.of_mapCocone, IsVanKampenColimit.precompose_isIso_iff, PushoutCocone, PushoutCocone.isoMk, diagramIsoSpan, hasPullback_of_mono_left, hasPushout_of_mono_left, isVanKampen_iff, of_iso, of_mapCocone, precompose_isIso_iff, van_kampen
-/
theorem adhesive_of_preserves_and_reflects (F : C ⥤ D) [Adhesive D]
    [H₁ : forall {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
    [H₂ : forall {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [ReflectsColimitsOfShape WalkingSpan F] :
    Adhesive C := by
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  refine IsVanKampenColimit.of_mapCocone F ?_
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map F)).mp ?_
  apply Adhesive.van_kampen

/--
theorem `adhesive_of_preserves_and_reflects_isomorphism` / 定理 `adhesive_of_preserves_and_reflects_isomorphism`

English:
theorem adhesive_of_preserves_and_reflects_isomorphism
  statement: (F : C ⥤ D)
  proof: by
  have : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape WalkingSpan F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact adhesive_of_preserves_and_reflects F

中文:
定理 adhesive_of_preserves_and_reflects_isomorphism
  结论: (F : C ⥤ D)
  证明: by
  have : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape WalkingSpan F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact adhesive_of_preserves_and_reflects F

Depends on / 依赖: ReflectsColimitsOfShape, ReflectsLimitsOfShape, WalkingCospan, WalkingSpan, adhesive_of_preserves_and_reflects, reflectsColimitsOfShape_of_reflectsIsomorphisms, reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
theorem adhesive_of_preserves_and_reflects_isomorphism (F : C ⥤ D)
    [Adhesive D] [HasPullbacks C] [HasPushouts C]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [F.ReflectsIsomorphisms] :
    Adhesive C := by
  have : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape WalkingSpan F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact adhesive_of_preserves_and_reflects F

/--
theorem `adhesive_of_reflective` / 定理 `adhesive_of_reflective`

English:
theorem adhesive_of_reflective
  statement: [HasPullbacks D] [Adhesive C] [HasPullbacks C] [HasPushouts C]
  proof: by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  apply Adhesive.mk (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i _ H
  have := Adhesive.van_kampen (IsPushout.of_hasPushout (Gr.map f) (Gr.map g))
  rw [IsPushout.isVanKampen_iff] at this ⊢
  refine 

中文:
定理 adhesive_of_reflective
  结论: [有Pullbacks D] [Adhesive C] [有Pullbacks C] [有Pushouts C]
  证明: by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  apply Adhesive.mk (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i _ H
  have := Adhesive.van_kampen (IsPushout.of_hasPushout (Gr.map f) (Gr.map g))
  rw [IsPushout.isVanKampen_iff] at this ⊢
  refine 

Depends on / 依赖: Adhesive, Adhesive.mk, Adhesive.van_kampen, Functor, Functor.isoWhiskerLeft, Functor.rightUnitor, Gr.map, IsColim, IsPushout, IsPushout.isVanKampen_iff, IsPushout.of_hasPushout, IsVanKampenColimit, IsVanKampenColimit.precompose_isIso_iff, adj.counit, adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits, counit, hasPushout_of_mono_left, isVanKampen_iff, isoWhiskerLeft
-/
theorem adhesive_of_reflective [HasPullbacks D] [Adhesive C] [HasPullbacks C] [HasPushouts C]
    [H₂ : forall {X Y S : D} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [PreservesLimitsOfShape WalkingCospan Gl] :
    Adhesive D := by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  apply Adhesive.mk (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i _ H
  have := Adhesive.van_kampen (IsPushout.of_hasPushout (Gr.map f) (Gr.map g))
  rw [IsPushout.isVanKampen_iff] at this ⊢
  refine (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp ?_
  refine ((this.precompose_isIso (spanCompIso _ _ _).hom).map_reflective adj).of_iso
    (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl ((IsColimit.precomposeHomEquiv _ _).symm <| pushoutIsPushout _ _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm H.isColimit

end functor

end CategoryTheory
