/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cover-lifting* or
*cover-reflecting functors*. We use the original terminology and definition of SGA 4 III 2.1.
However, the notion of cocontinuous functor should not be confused with
the general definition of cocontinuous functors between categories as functors preserving
small colimits.

## Main definitions

* `CategoryTheory.Functor.IsCocontinuous`: a functor between sites is cocontinuous if it
  pulls back covering sieves to covering sieves
* `CategoryTheory.Functor.sheafPushforwardCocontinuous`: A cocontinuous functor
  `G : (C, J) ⥤ (D, K)` induces a functor `Sheaf J A ⥤ Sheaf K A`.

## Main results
* `CategoryTheory.ran_isSheaf_of_isCocontinuous`: If `G : C ⥤ D` is cocontinuous, then
  `G.op.ran` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Functor.sheafAdjunctionCocontinuous`: If `G : (C, J) ⥤ (D, K)` is cocontinuous
  and continuous, then `G.sheafPushforwardContinuous A J K` and
  `G.sheafPushforwardCocontinuous A J K` are adjoint.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

@[expose] public section


universe w' w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

section IsCocontinuous

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E] (G : C ⥤ D)
  (G' : D ⥤ E)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/--
Definition of `Functor.IsCocontinuous` / `Functor.IsCocontinuous` 的定义

English:
class Functor.IsCocontinuous
  parameters: : Prop where
  axioms and operations (1):
    - cover_lift : forall {U : C} {S : Sieve (G.obj U)} (_ : S in K (G.obj U)), S.functorPullback G in J U

中文:
类 Functor.IsCocontinuous
  参数: : 命题 where
  公理与运算 (1 个):
    - cover_lift : 对任意 {U : C} {S : Sieve (G.obj U)} (_ : S in K (G.obj U)), S.functorPullback G in J U
-/
class Functor.IsCocontinuous : Prop where
  cover_lift : forall {U : C} {S : Sieve (G.obj U)} (_ : S in K (G.obj U)), S.functorPullback G in J U

/--
lemma `Functor.cover_lift` / 引理 `Functor.cover_lift`

English:
lemma Functor.cover_lift
  statement: [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
  proof: IsCocontinuous.cover_lift hS

中文:
引理 Functor.cover_lift
  结论: [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
  证明: IsCocontinuous.cover_lift hS

Depends on / 依赖: IsCocontinuous, IsCocontinuous.cover_lift, cover_lift
-/
lemma Functor.cover_lift [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
    (hS : S in K (G.obj U)) : S.functorPullback G in J U :=
  IsCocontinuous.cover_lift hS

/--
Instance `isCocontinuous_id` / 实例 `isCocontinuous_id`

English:
instance isCocontinuous_id
  signature: : Functor.IsCocontinuous (𝟭 C) J J
  body: ⟨fun h => by simpa using! h⟩

中文:
实例 isCocontinuous_id
  签名: : Functor.IsCocontinuous (𝟭 C) J J
  定义体: ⟨fun h => by simpa using! h⟩
-/
instance isCocontinuous_id : Functor.IsCocontinuous (𝟭 C) J J :=
  ⟨fun h => by simpa using! h⟩

/--
theorem `isCocontinuous_comp` / 定理 `isCocontinuous_comp`

English:
theorem isCocontinuous_comp
  given: [G.IsCocontinuous J K] [G'.IsCocontinuous K L]
  proof: G.cover_lift J K (G'.cover_lift K L h)

中文:
定理 isCocontinuous_comp
  条件: [G.IsCocontinuous J K] [G'.IsCocontinuous K L]
  证明: G.cover_lift J K (G'.cover_lift K L h)

Depends on / 依赖: G.cover_lift, cover_lift
-/
theorem isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] :
    (G ⋙ G').IsCocontinuous J L where
  cover_lift h := G.cover_lift J K (G'.cover_lift K L h)

variable {J K} in
/--
lemma `Functor.IsCocontinuous.of_iso` / 引理 `Functor.IsCocontinuous.of_iso`

English:
lemma Functor.IsCocontinuous.of_iso
  given: {F G : C ⥤ D} (e : F ≅ G) [F.IsCocontinuous J K]
  proof: by
    refine J.superset_covering ?_ (F.cover_lift J K (K.pullback_stable (e.hom.app U) hS))
    intro Y f (hf : S.arrows (F.map f ≫ e.hom.app U))
    have := S.downward_closed hf (e.inv.app Y)
    rwa [e.hom.naturality f, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at this

中文:
引理 Functor.IsCocontinuous.of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G) [F.IsCocontinuous J K]
  证明: by
    refine J.superset_covering ?_ (F.cover_lift J K (K.pullback_stable (e.hom.app U) hS))
    intro Y f (hf : S.arrows (F.map f ≫ e.hom.app U))
    have := S.downward_closed hf (e.inv.app Y)
    rwa [e.hom.naturality f, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at this

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.cover_lift, F.map, Iso.inv_hom_id_app, J.superset_covering, K.pullback_stable, S.arrows, S.downward_closed, arrows, cover_lift, downward_closed, e.hom.app, e.hom.naturality, e.inv.app, id_comp, inv_hom_id_app, naturality, pullback_stable
-/
lemma Functor.IsCocontinuous.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsCocontinuous J K] :
    G.IsCocontinuous J K where
  cover_lift {U} S hS := by
    refine J.superset_covering ?_ (F.cover_lift J K (K.pullback_stable (e.hom.app U) hS))
    intro Y f (hf : S.arrows (F.map f ≫ e.hom.app U))
    have := S.downward_closed hf (e.inv.app Y)
    rwa [e.hom.naturality f, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at this

variable {J K} in
/--
lemma `Functor.IsCocontinuous.iff_of_iso` / 引理 `Functor.IsCocontinuous.iff_of_iso`

English:
lemma Functor.IsCocontinuous.iff_of_iso
  given: {F G : C ⥤ D} (e : F ≅ G)
  proof: ⟨fun _ => .of_iso e, fun _ => .of_iso e.symm⟩

中文:
引理 Functor.IsCocontinuous.iff_of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G)
  证明: ⟨fun _ => .of_iso e, fun _ => .of_iso e.symm⟩

Depends on / 依赖: e.symm, of_iso
-/
lemma Functor.IsCocontinuous.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsCocontinuous J K ↔ G.IsCocontinuous J K :=
  ⟨fun _ => .of_iso e, fun _ => .of_iso e.symm⟩

/--
lemma `CoverPreserving.of_comp_of_isCocontinuous` / 引理 `CoverPreserving.of_comp_of_isCocontinuous`

English:
lemma CoverPreserving.of_comp_of_isCocontinuous
  statement: {F : C ⥤ D} (G : D ⥤ E)
  proof: by
    refine K.superset_covering ?_ (G.cover_lift K _ (h.cover_preserve hS))
    rw [Sieve.functorPushforward_comp]; rw [Sieve.functorPullback_functorPushforward_eq G]

中文:
引理 CoverPreserving.of_comp_of_isCocontinuous
  结论: {F : C ⥤ D} (G : D ⥤ E)
  证明: by
    refine K.superset_covering ?_ (G.cover_lift K _ (h.cover_preserve hS))
    rw [Sieve.functorPushforward_comp]; rw [Sieve.functorPullback_functorPushforward_eq G]

Depends on / 依赖: G.cover_lift, K.superset_covering, Sieve.functorPullback_functorPushforward_eq, Sieve.functorPushforward_comp, cover_lift, cover_preserve, functorPullback_functorPushforward_eq, functorPushforward_comp, h.cover_preserve, superset_covering
-/
lemma CoverPreserving.of_comp_of_isCocontinuous {F : C ⥤ D} (G : D ⥤ E)
    (h : CoverPreserving J L (F ⋙ G)) [G.IsCocontinuous K L] [G.Full] [G.Faithful] :
    CoverPreserving J K F where
  cover_preserve {U} S hS := by
    refine K.superset_covering ?_ (G.cover_lift K _ (h.cover_preserve hS))
    rw [Sieve.functorPushforward_comp]; rw [Sieve.functorPullback_functorPushforward_eq G]

section

variable {F : C ⥤ D} {G : D ⥤ C}

/--
lemma `Adjunction.isCocontinuous_iff_coverPreserving` / 引理 `Adjunction.isCocontinuous_iff_coverPreserving`

English:
lemma Adjunction.isCocontinuous_iff_coverPreserving
  given: (adj : F ⊣ G)
  proof: by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · intro U S hS
refine J.superset_covering ?_ h.cover_lift (K.pullback_stable (adj.counit.app _) hS)
    intro X f hf
    refine ⟨F.obj X, F.map f ≫ adj.counit.app _, adj.unit.app _, hf, by simp⟩
  · intro U S hS
    refine J.superset_covering ?_ (J.pullba

中文:
引理 Adjunction.isCocontinuous_iff_coverPreserving
  条件: (adj : F ⊣ G)
  证明: by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · intro U S hS
refine J.superset_covering ?_ h.cover_lift (K.pullback_stable (adj.counit.app _) hS)
    intro X f hf
    refine ⟨F.obj X, F.map f ≫ adj.counit.app _, adj.unit.app _, hf, by simp⟩
  · intro U S hS
    refine J.superset_covering ?_ (J.pullba

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right_symm, F.map, F.obj, J.pullback_stable, J.superset_covering, K.pullback_stable, S.downward_closed, adj.counit.app, adj.homEquiv, adj.unit.app, counit, cover_lift, cover_preserve, downward_closed, h.cover_lift, h.cover_preserve, homEquiv, homEquiv_naturality_right_symm, pullback_stable
-/
lemma Adjunction.isCocontinuous_iff_coverPreserving (adj : F ⊣ G) :
    F.IsCocontinuous J K ↔ CoverPreserving K J G := by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · intro U S hS
refine J.superset_covering ?_ h.cover_lift (K.pullback_stable (adj.counit.app _) hS)
    intro X f hf
    refine ⟨F.obj X, F.map f ≫ adj.counit.app _, adj.unit.app _, hf, by simp⟩
  · intro U S hS
    refine J.superset_covering ?_ (J.pullback_stable (adj.unit.app U) <| h.cover_preserve hS)
    intro X f ⟨Y, g, u, hg, heq⟩
    suffices F.map f = (adj.homEquiv _ _).symm u ≫ g by
      simp [this, S.downward_closed hg]
    simp [← Adjunction.homEquiv_naturality_right_symm, ← heq,
      Adjunction.homEquiv_naturality_left_symm]

/--
lemma `Adjunction.isContinuous_of_isCocontinuous` / 引理 `Adjunction.isContinuous_of_isCocontinuous`

English:
lemma Adjunction.isContinuous_of_isCocontinuous
  given: (adj : F ⊣ G) [F.IsCocontinuous J K]
  proof: by
  have := adj.isRightAdjoint
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat J G)
  rwa [← adj.isCocontinuous_iff_coverPreserving]

中文:
引理 Adjunction.isContinuous_of_isCocontinuous
  条件: (adj : F ⊣ G) [F.IsCocontinuous J K]
  证明: by
  have := adj.isRightAdjoint
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat J G)
  rwa [← adj.isCocontinuous_iff_coverPreserving]

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, adj.isCocontinuous_iff_coverPreserving, adj.isRightAdjoint, compatiblePreservingOfFlat, isCocontinuous_iff_coverPreserving, isContinuous_of_coverPreserving, isRightAdjoint
-/
lemma Adjunction.isContinuous_of_isCocontinuous (adj : F ⊣ G) [F.IsCocontinuous J K] :
    G.IsContinuous K J := by
  have := adj.isRightAdjoint
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat J G)
  rwa [← adj.isCocontinuous_iff_coverPreserving]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsCocontinuous
  signature: J K] [F.IsLeftAdjoint] : F.rightAdjoint.IsContinuous K J
  body: (Adjunction.ofIsLeftAdjoint F).isContinuous_of_isCocontinuous J K

中文:
实例 [F.IsCocontinuous
  签名: J K] [F.IsLeftAdjoint] : F.rightAdjoint.IsContinuous K J
  定义体: (Adjunction.ofIsLeftAdjoint F).isContinuous_of_isCocontinuous J K

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, isContinuous_of_isCocontinuous, ofIsLeftAdjoint
-/
instance [F.IsCocontinuous J K] [F.IsLeftAdjoint] : F.rightAdjoint.IsContinuous K J :=
  (Adjunction.ofIsLeftAdjoint F).isContinuous_of_isCocontinuous J K

end

end IsCocontinuous

/-!
We will now prove that `G.op.ran : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` maps sheaves
to sheaves when `G : C ⥤ D` is a cocontinuous functor.

We do not follow the proofs in SGA 4 III 2.2 or <https://stacks.math.columbia.edu/tag/00XK>.
Instead, we verify as directly as possible that if `F : Cᵒᵖ ⥤ A` is a sheaf,
then `G.op.ran.obj F` is a sheaf. In order to do this, we use the "multifork"
characterization of sheaves which involves limits in the category `A`.
As `G.op.ran.obj F` is the chosen right Kan extension of `F` along `G.op : Cᵒᵖ ⥤ Dᵒᵖ`,
we actually verify that any pointwise right Kan extension of `F` along `G.op` is a sheaf.

-/

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
variable {A : Type w} [Category.{w'} A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsCocontinuous J K]

namespace RanIsSheafOfIsCocontinuous

variable {G}
variable {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)
variable {R : Dᵒᵖ ⥤ A} (α : G.op ⋙ R ⟶ F)
variable (hR : (Functor.RightExtension.mk _ α).IsPointwiseRightKanExtension)
variable {X : D} {S : K.Cover X} (s : Multifork (S.index R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: {Y : C} (f : G.obj Y ⟶ X)
  body: Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k => s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← 

中文:
定义 liftAux
  签名: {Y : C} (f : G.obj Y ⟶ X)
  定义体: Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k => s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← 

Depends on / 依赖: Category, Category.assoc, Functor, Functor.comp_map, Functor.op_map, G.congr_map, G.cover_lift, G.map, IsLimit, K.pullback_stable, Multifork, Multifork.IsLimit.lift, Quiver, Quiver.Hom.unop_op, comp_map, condition_assoc, congr_map, cover_lift, fst.hf, hF.isLimitMultifork
-/
def liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y) :=
  Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k => s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← α.naturality, Functor.comp_map,
        Functor.op_map, Quiver.Hom.unop_op]
      apply s.condition_assoc
        { fst.hf := hp₁
          snd.hf := hp₂
          r.g₁ := G.map g₁
          r.g₂ := G.map g₂
          r.w := by simpa using G.congr_map w =≫ f
          .. })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `liftAux_map` / 引理 `liftAux_map`

English:
lemma liftAux_map
  statement: {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
  proof: (Multifork.IsLimit.fac
    (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩) _ _
      ⟨W, g, by simpa only [Sieve.functorPullback_apply, functorPullback_mem,
        Sieve.pullback_apply, ← w] using S.1.downward_closed i.hf h⟩).trans (by
        dsimp
        simp only [← Catego

中文:
引理 liftAux_map
  结论: {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
  证明: (Multifork.IsLimit.fac
    (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩) _ _
      ⟨W, g, by simpa only [Sieve.functorPullback_apply, functorPullback_mem,
        Sieve.pullback_apply, ← w] using S.1.downward_closed i.hf h⟩).trans (by
        dsimp
        simp only [← Catego

Depends on / 依赖: Category, Category.assoc, G.cover_lift, G.map, IsLimit, K.pullback_stable, Multifork, Multifork.IsLimit.fac, Relation, S.Relation, Sieve.functorPullback_apply, Sieve.pullback_apply, condition, cover_lift, downward_closed, fst.f, fst.hf, functorPullback_apply, functorPullback_mem, hF.isLimitMultifork
-/
lemma liftAux_map {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
    (h : G.obj W ⟶ i.Y) (w : h ≫ i.f = G.map g ≫ f) :
    liftAux hF α s f ≫ F.map g.op = s.ι i ≫ R.map h.op ≫ α.app _ :=
  (Multifork.IsLimit.fac
    (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩) _ _
      ⟨W, g, by simpa only [Sieve.functorPullback_apply, functorPullback_mem,
        Sieve.pullback_apply, ← w] using S.1.downward_closed i.hf h⟩).trans (by
        dsimp
        simp only [← Category.assoc]
        congr 1
        let r : S.Relation :=
          { fst.f := G.map g ≫ f
            fst.hf := by simpa only [← w] using S.1.downward_closed i.hf h
            snd := i
            r.g₁ := 𝟙 _
            r.g₂ := h
            r.w := by simpa using w.symm
            .. }
        simpa [r] using s.condition r)

/--
lemma `liftAux_map'` / 引理 `liftAux_map'`

English:
lemma liftAux_map'
  statement: {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
  proof: by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_c

中文:
引理 liftAux_map'
  结论: {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
  证明: by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_c

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.map_id, G.cover_lift, G.map, K.pullback_stable, cover_lift, hF.hom_ext, hom_ext, liftAux_map, map_comp, map_id, pullback_stable
-/
lemma liftAux_map' {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
    (a : W ⟶ Y) (b : W ⟶ Y') (w : G.map a ≫ f = G.map b ≫ f') :
    liftAux hF α s f ≫ F.map a.op = liftAux hF α s f' ≫ F.map b.op := by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_comp, Functor.map_id] at eq₁ eq₂
  simp only [Category.assoc, eq₁, eq₂]

variable {α}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : s.pt ⟶ R.obj (op X)
  body: (hR (op X)).lift (Cone.mk _
    { app := fun j => liftAux hF α s j.hom.unop
      naturality := fun j j' φ => by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })

中文:
定义 lift
  签名: : s.pt ⟶ R.obj (op X)
  定义体: (hR (op X)).lift (Cone.mk _
    { app := fun j => liftAux hF α s j.hom.unop
      naturality := fun j j' φ => by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })

Depends on / 依赖: Cone.mk, Quiver, Quiver.Hom.op_inj, StructuredArrow, StructuredArrow.w, hom.unop, j.hom.unop, liftAux, liftAux_map, naturality, op_inj, right.unop
-/
def lift : s.pt ⟶ R.obj (op X) :=
  (hR (op X)).lift (Cone.mk _
    { app := fun j => liftAux hF α s j.hom.unop
      naturality := fun j j' φ => by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })

/--
lemma `fac'` / 引理 `fac'`

English:
lemma fac'
  given: (j : StructuredArrow (op X) G.op)
  proof: by
  apply IsLimit.fac

中文:
引理 fac'
  条件: (j : StructuredArrow (op X) G.op)
  证明: by
  apply IsLimit.fac

Depends on / 依赖: IsLimit, IsLimit.fac
-/
lemma fac' (j : StructuredArrow (op X) G.op) :
    lift hF hR s ≫ R.map j.hom ≫ α.app j.right = liftAux hF α s j.hom.unop := by
  apply IsLimit.fac

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: (i : S.Arrow)
  statement: lift hF hR s ≫ R.map i.f.op = s.ι i
  proof: by
  apply (hR (op i.Y)).hom_ext
  intro j
  have eq := fac' hF hR s (StructuredArrow.mk (i.f.op ≫ j.hom))
  dsimp at eq ⊢
  simp only [Functor.map_comp, Category.assoc] at eq
  rw [Category.assoc]; rw [eq]
  simpa using liftAux_map hF α s (j.hom.unop ≫ i.f) (𝟙 _) i j.hom.unop (by simp)

中文:
引理 fac
  条件: (i : S.Arrow)
  结论: lift hF hR s ≫ R.map i.f.op = s.ι i
  证明: by
  apply (hR (op i.Y)).hom_ext
  intro j
  have eq := fac' hF hR s (StructuredArrow.mk (i.f.op ≫ j.hom))
  dsimp at eq ⊢
  simp only [Functor.map_comp, Category.assoc] at eq
  rw [Category.assoc]; rw [eq]
  simpa using liftAux_map hF α s (j.hom.unop ≫ i.f) (𝟙 _) i j.hom.unop (by simp)

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, StructuredArrow, StructuredArrow.mk, hom_ext, i.f.op, j.hom, j.hom.unop, liftAux_map, map_comp
-/
lemma fac (i : S.Arrow) : lift hF hR s ≫ R.map i.f.op = s.ι i := by
  apply (hR (op i.Y)).hom_ext
  intro j
  have eq := fac' hF hR s (StructuredArrow.mk (i.f.op ≫ j.hom))
  dsimp at eq ⊢
  simp only [Functor.map_comp, Category.assoc] at eq
  rw [Category.assoc]; rw [eq]
  simpa using liftAux_map hF α s (j.hom.unop ≫ i.f) (𝟙 _) i j.hom.unop (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hR hF in
variable (K) in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {W : A} {f g : W ⟶ R.obj (op X)}
  proof: by
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_ma

中文:
引理 hom_ext
  结论: {W : A} {f g : W ⟶ R.obj (op X)}
  证明: by
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_ma

Depends on / 依赖: Category, Category.assoc, Functor, Functor.comp_map, Functor.map_comp_assoc, Functor.op_map, G.cover_lift, G.map, GrothendieckTopology, GrothendieckTopology.Cover.Arrow.mk, K.pullback_stable, NatTrans, NatTrans.naturality, Quiver, Quiver.Hom.unop_op, comp_map, cover_lift, hF.hom_ext, hom_ext, j.hom.unop
-/
lemma hom_ext {W : A} {f g : W ⟶ R.obj (op X)}
    (h : forall (i : S.Arrow), f ≫ R.map i.f.op = g ≫ R.map i.f.op) : f = g := by
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    Functor.op_map, Quiver.Hom.unop_op]
  rw [reassoc_of% eq]

variable (S)

/--
Definition of `isLimitMultifork` / `isLimitMultifork` 的定义

English:
definition isLimitMultifork
  signature: : IsLimit (S.multifork R)
  body: Multifork.IsLimit.mk _ (lift hF hR) (fac hF hR)
    (fun s _ hm => hom_ext K hF hR (fun i => (hm i).trans (fac hF hR s i).symm))

中文:
定义 isLimitMultifork
  签名: : IsLimit (S.multifork R)
  定义体: Multifork.IsLimit.mk _ (lift hF hR) (fac hF hR)
    (fun s _ hm => hom_ext K hF hR (fun i => (hm i).trans (fac hF hR s i).symm))

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.mk, hom_ext
-/
def isLimitMultifork : IsLimit (S.multifork R) :=
  Multifork.IsLimit.mk _ (lift hF hR) (fac hF hR)
    (fun s _ hm => hom_ext K hF hR (fun i => (hm i).trans (fac hF hR s i).symm))

end RanIsSheafOfIsCocontinuous

variable (K)
variable [forall (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]

/-- If `G` is cocontinuous, then `G.op.ran` pushes sheaves to sheaves.

This is SGA 4 III 2.2. -/
@[stacks 00XK "Alternative reference. There, results are obtained under the additional assumption
that `C` and `D` have pullbacks."]
/--
theorem `ran_isSheaf_of_isCocontinuous` / 定理 `ran_isSheaf_of_isCocontinuous`

English:
theorem ran_isSheaf_of_isCocontinuous
  given: (ℱ : Sheaf J A)
  proof: by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.obj) S⟩

中文:
定理 ran_isSheaf_of_isCocontinuous
  条件: (ℱ : Sheaf J A)
  证明: by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.obj) S⟩

Depends on / 依赖: G.op.isPointwiseRightKanExtensionRanCounit, Presheaf, Presheaf.isSheaf_iff_multifork, RanIsSheafOfIsCocontinuous, RanIsSheafOfIsCocontinuous.isLimitMultifork, isLimitMultifork, isPointwiseRightKanExtensionRanCounit, isSheaf_iff_multifork
-/
theorem ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K (G.op.ran.obj ℱ.obj) := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.obj) S⟩

variable (A J)

/--
Definition of `Functor.sheafPushforwardCocontinuous` / `Functor.sheafPushforwardCocontinuous` 的定义

English:
definition Functor.sheafPushforwardCocontinuous
  signature: : Sheaf J A ⥤ Sheaf K A
  body: ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ G.op.ran) (ran_isSheaf_of_isCocontinuous _ K)

中文:
定义 Functor.sheafPushforwardCocontinuous
  签名: : Sheaf J A ⥤ Sheaf K A
  定义体: ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ G.op.ran) (ran_isSheaf_of_isCocontinuous _ K)

Depends on / 依赖: G.op.ran, ObjectProperty, ObjectProperty.lift, ran_isSheaf_of_isCocontinuous, sheafToPresheaf
-/
def Functor.sheafPushforwardCocontinuous : Sheaf J A ⥤ Sheaf K A :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ G.op.ran) (ran_isSheaf_of_isCocontinuous _ K)

/-- `G.sheafPushforwardCocontinuous A J K : Sheaf J A ⥤ Sheaf K A` is induced
by the right Kan extension functor `G.op.ran` on presheaves. -/
@[simps! hom inv]
/--
Definition of `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso` / `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso` 的定义

English:
definition Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
  signature: :
  body: Iso.refl _

中文:
定义 Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso :
    G.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ G.op.ran := Iso.refl _

/-

Given a cocontinuous functor `G`, the precomposition with `G.op` induces a functor
on presheaves with leads to a "pullback" functor `Sheaf K A ⥤ Sheaf J A` (TODO: formalize
this as `G.sheafPullbackCocontinuous A J K`) using the associated sheaf functor.
It is shown in SGA 4 III 2.3 that this pullback functor is
left adjoint to `G.sheafPushforwardCocontinuous A J K`. This adjunction may replace
`Functor.sheafAdjunctionCocontinuous` below, and then, it could be shown that if
`G` is also continuous, then we have an isomorphism
`G.sheafPullbackCocontinuous A J K ≅ G.sheafPushforwardContinuous A J K` (TODO).

-/

namespace Functor

variable [G.IsContinuous J K]

/--
Definition of `sheafAdjunctionCocontinuous` / `sheafAdjunctionCocontinuous` 的定义

English:
definition sheafAdjunctionCocontinuous
  signature: :
  body: (G.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm

中文:
定义 sheafAdjunctionCocontinuous
  签名: :
  定义体: (G.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm

Depends on / 依赖: G.op.ranAdjunction, G.sheafPushforwardCocontinuousCompSheafToPresheafIso, G.sheafPushforwardContinuousCompSheafToPresheafIso, fullyFaithfulSheafToPresheaf, ranAdjunction, restrictFullyFaithful, sheafPushforwardCocontinuousCompSheafToPresheafIso, sheafPushforwardContinuousCompSheafToPresheafIso
-/
noncomputable def sheafAdjunctionCocontinuous :
    G.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardCocontinuous A J K :=
  (G.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm

/--
lemma `sheafAdjunctionCocontinuous_unit_app_hom` / 引理 `sheafAdjunctionCocontinuous_unit_app_hom`

English:
lemma sheafAdjunctionCocontinuous_unit_app_hom
  given: (F : Sheaf K A)
  proof: by
  apply ((G.op.ranAdjunction A).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
  dsimp
 

中文:
引理 sheafAdjunctionCocontinuous_unit_app_hom
  条件: (F : Sheaf K A)
  证明: by
  apply ((G.op.ranAdjunction A).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
  dsimp
 

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.map_id, G.op.ranAdjunction, G.sheafPushforwardCocontinuousCompSheafToPresheafIso, G.sheafPushforwardContinuousCompSheafToPresheafIso, comp_id, fullyFaithfulSheafToPresheaf, map_id, map_restrictFullyFaithful_unit_app, ranAdjunction, sheafPushforwardCocontinuousCompSheafToPresheafIso, sheafPushforwardContinuousCompSheafToPresheafIso
-/
lemma sheafAdjunctionCocontinuous_unit_app_hom (F : Sheaf K A) :
    ((G.sheafAdjunctionCocontinuous A J K).unit.app F).hom =
      (G.op.ranAdjunction A).unit.app F.obj := by
  apply ((G.op.ranAdjunction A).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
  dsimp
  erw [Functor.map_id]
  change _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_unit_app_val :=
  sheafAdjunctionCocontinuous_unit_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sheafAdjunctionCocontinuous_counit_app_hom` / 引理 `sheafAdjunctionCocontinuous_counit_app_hom`

English:
lemma sheafAdjunctionCocontinuous_counit_app_hom
  given: (F : Sheaf J A)
  proof: ((G.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
      (by cat_disc

中文:
引理 sheafAdjunctionCocontinuous_counit_app_hom
  条件: (F : Sheaf J A)
  证明: ((G.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
      (by cat_disc

Depends on / 依赖: G.op.ranAdjunction, G.sheafPushforwardCocontinuousCompSheafToPresheafIso, G.sheafPushforwardContinuousCompSheafToPresheafIso, cat_disch, fullyFaithfulSheafToPresheaf, map_restrictFullyFaithful_counit_app, ranAdjunction, sheafPushforwardCocontinuousCompSheafToPresheafIso, sheafPushforwardContinuousCompSheafToPresheafIso
-/
lemma sheafAdjunctionCocontinuous_counit_app_hom (F : Sheaf J A) :
    ((G.sheafAdjunctionCocontinuous A J K).counit.app F).hom =
      (G.op.ranAdjunction A).counit.app F.obj :=
  ((G.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
      (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_counit_app_val :=
  sheafAdjunctionCocontinuous_counit_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sheafAdjunctionCocontinuous_homEquiv_apply_hom` / 引理 `sheafAdjunctionCocontinuous_homEquiv_apply_hom`

English:
lemma sheafAdjunctionCocontinuous_homEquiv_apply_hom
  statement: {F : Sheaf K A} {H : Sheaf J A}
  proof: ((sheafToPresheaf K A).congr_map
    (((G.op.ranAdjunction A).restrictFullyFaithful_homEquiv_apply
      (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (G.sheafPushforwardCocontinuousCompSheafToPreshea

中文:
引理 sheafAdjunctionCocontinuous_homEquiv_apply_hom
  结论: {F : Sheaf K A} {H : Sheaf J A}
  证明: ((sheafToPresheaf K A).congr_map
    (((G.op.ranAdjunction A).restrictFullyFaithful_homEquiv_apply
      (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (G.sheafPushforwardCocontinuousCompSheafToPreshea

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Category, Category.comp_id, Category.id_comp, Functor, Functor.map_id, G.op.ranAdjunction, G.sheafPushforwardCocontinuousCompSheafToPresheafIso, G.sheafPushforwardContinuousCompSheafToPresheafIso, comp_id, congr_map, fullyFaithfulSheafToPresheaf, homEquiv_unit, id_comp, map_id, ranAdjunction, restrictFullyFaithful_homEquiv_apply, sheafPushforwardCocontinuousCompSheafToPresheafIso, sheafPushforwardContinuousCompSheafToPresheafIso
-/
lemma sheafAdjunctionCocontinuous_homEquiv_apply_hom {F : Sheaf K A} {H : Sheaf J A}
    (f : (G.sheafPushforwardContinuous A J K).obj F ⟶ H) :
    ((G.sheafAdjunctionCocontinuous A J K).homEquiv F H f).hom =
      (G.op.ranAdjunction A).homEquiv F.obj H.obj f.hom :=
  ((sheafToPresheaf K A).congr_map
    (((G.op.ranAdjunction A).restrictFullyFaithful_homEquiv_apply
      (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm f))).trans (by
        dsimp
        erw [Functor.map_id, Category.comp_id, Category.id_comp,
          Adjunction.homEquiv_unit])

@[deprecated (since := "2026-03-05")]
alias sheafAdjunctionCocontinuous_homEquiv_apply_val :=
  sheafAdjunctionCocontinuous_homEquiv_apply_hom

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/--
Definition of `pushforwardContinuousSheafificationCompatibility` / `pushforwardContinuousSheafificationCompatibility` 的定义

English:
definition pushforwardContinuousSheafificationCompatibility
  signature: :
  body: ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

中文:
定义 pushforwardContinuousSheafificationCompatibility
  签名: :
  定义体: ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

Depends on / 依赖: G.op.ranAdjunction, G.sheafAdjunctionCocontinuous, leftAdjointUniq, ranAdjunction, sheafAdjunctionCocontinuous, sheafificationAdjunction
-/
def pushforwardContinuousSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K :=
  ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSheafify_pullbackSheafificationCompatibility` / 引理 `toSheafify_pullbackSheafificationCompatibility`

English:
lemma toSheafify_pullbackSheafificationCompatibility
  given: (F : Dᵒᵖ ⥤ A)
  proof: by
  let adj₁ := G.op.ranAdjunction A
  let adj₂ := sheafificationAdjunction J A
  let adj₃ := sheafificationAdjunction K A
  let adj₄ := G.sheafAdjunctionCocontinuous A J K
  change adj₂.unit.app (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj F) ≫
    (sheafToPresheaf J A).map (((adj₁.comp adj₂).leftAd

中文:
引理 toSheafify_pullbackSheafificationCompatibility
  条件: (F : Dᵒᵖ ⥤ A)
  证明: by
  let adj₁ := G.op.ranAdjunction A
  let adj₂ := sheafificationAdjunction J A
  let adj₃ := sheafificationAdjunction K A
  let adj₄ := G.sheafAdjunctionCocontinuous A J K
  change adj₂.unit.app (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj F) ≫
    (sheafToPresheaf J A).map (((adj₁.comp adj₂).leftAd

Depends on / 依赖: G.op, G.op.ranAdjunction, G.sheafAdjunctionCocontinuous, hom.app, homEquiv, injective, leftAdjointUniq, ranAdjunction, sheafAdjunctionCocontinuous, sheafToPresheaf, sheafificationAdjunction, unit.app, unit_leftAdjointUniq_hom_app, whiskeringLeft
-/
lemma toSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ F) ≫
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom =
    whiskerLeft _ (toSheafify K _) := by
  let adj₁ := G.op.ranAdjunction A
  let adj₂ := sheafificationAdjunction J A
  let adj₃ := sheafificationAdjunction K A
  let adj₄ := G.sheafAdjunctionCocontinuous A J K
  change adj₂.unit.app (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj F) ≫
    (sheafToPresheaf J A).map (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F) =
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map (adj₃.unit.app F)
  apply (adj₁.homEquiv _ _).injective
  have eq := (adj₁.comp adj₂).unit_leftAdjointUniq_hom_app (adj₃.comp adj₄) F
  rw [Adjunction.comp_unit_app]; rw [Adjunction.comp_unit_app]; rw [comp_map]; rw [Category.assoc] at eq
  rw [adj₁.homEquiv_unit]; rw [Functor.map_comp]; rw [eq]
  apply (adj₁.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, map_comp, Category.assoc,
    Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  congr 3
  exact G.sheafAdjunctionCocontinuous_unit_app_hom A J K ((presheafToSheaf K A).obj F)

@[simp]
/--
lemma `pushforwardContinuousSheafificationCompatibility_hom_app_hom` / 引理 `pushforwardContinuousSheafificationCompatibility_hom_app_hom`

English:
lemma pushforwardContinuousSheafificationCompatibility_hom_app_hom
  given: (F : Dᵒᵖ ⥤ A)
  proof: by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

@[deprecated (since := "2026-03-05")]
alias pushforwardContinuousSheafificationCompatibility_hom_app_val :=
  pushforwardContinuousSheafificationCompatibility_hom_app_hom

中文:
引理 pushforwardContinuousSheafificationCompatibility_hom_app_hom
  条件: (F : Dᵒᵖ ⥤ A)
  证明: by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

@[deprecated (since := "2026-03-05")]
alias pushforwardContinuousSheafificationCompatibility_hom_app_val :=
  pushforwardContinuousSheafificationCompatibility_hom_app_hom

Depends on / 依赖: sheafifyLift_unique, toSheafify_pullbackSheafificationCompatibility
-/
lemma pushforwardContinuousSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom =
    sheafifyLift J (whiskerLeft G.op <| toSheafify K F)
      ((presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K).obj F).property := by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

@[deprecated (since := "2026-03-05")]
alias pushforwardContinuousSheafificationCompatibility_hom_app_val :=
  pushforwardContinuousSheafificationCompatibility_hom_app_hom

end Functor

end CategoryTheory
