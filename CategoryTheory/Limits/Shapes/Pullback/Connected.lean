/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!

# Pullbacks commute with connected limits

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/--
Let `F` and `G` be two diagrams indexed by a connected `I`, and `X` and `Y` be two cones over
`F` and `G` respectively, with maps `α : F ⟶ G` and `f : X ⟶ Y` that commutes with the cone maps.
Suppose `X = Y x[G i] F i` for all `i` and `Y = lim G`, then `X = lim F`.
-/
noncomputable
/-
**CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfIsPullbackOfIsConnected {I C : Type*} [Category* I] [IsConnected 
I] [Category* C] {F G : I ⥤ C} (α : F ⟶ G) (cF : Cone F) (cG : Cone G) (f : (Con
e.postcompose α).obj cF ⟶ cG) (hf : forall i, IsPullback (cF.π.app i) f.hom (α.a
pp i) (cG.π.app i)) (hcG : IsLimit cG) : IsLimit cF where lift s
参数：α : F ⟶ G；cF : Cone F；cG : Cone G；f : (Cone.postcompose α).obj cF ⟶ cG；hf : f
orall i, IsPullback (cF.π.app i) f.hom (α.app i) (cG.π.app i)；hcG : IsLimit cG。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
-/
def isLimitOfIsPullbackOfIsConnected
    {I C : Type*} [Category* I] [IsConnected I] [Category* C] {F G : I ⥤ C}
    (α : F ⟶ G) (cF : Cone F) (cG : Cone G)
    (f : (Cone.postcompose α).obj cF ⟶ cG)
    (hf : ∀ i, IsPullback (cF.π.app i) f.hom (α.app i) (cG.π.app i))
    (hcG : IsLimit cG) : IsLimit cF where
  lift s := (hf (Classical.arbitrary _)).lift
    (s.π.app (Classical.arbitrary _)) (hcG.lift ((Cone.postcompose α).obj s)) (by simp)
  fac s j := by
    let f (i : _) : s.pt ⟶ cF.pt :=
      (hf i).lift (s.π.app i) (hcG.lift ((Cone.postcompose α).obj s)) (by simp)
    have (i j : _) : f i = f j := by
      refine constant_of_preserves_morphisms f (fun j₁ j₂ g ↦ ?_) i j
      refine (hf j₂).hom_ext ?_ (by simp [f])
      rw [IsPullback.lift_fst, ← cF.w g, IsPullback.lift_fst_assoc, Cone.w]
    change f _ ≫ _ = _
    rw [this _ j]
    simp [f]
  uniq s g hg := (hf (Classical.arbitrary _)).hom_ext (by simp [hg])
    (hcG.hom_ext <| by simp [reassoc_of% hg])

set_option backward.isDefEq.respectTransparency false in
/--
Let `F` and `G` be two diagrams indexed by a connected `I`, and `X` and `Y` be two cocones over
`F` and `G` respectively, with maps `α : F ⟶ G` and `f : X ⟶ Y` that commutes with the cocone maps.
Suppose `Y = X ⨿[F i] G i` for all `i` and `Y = colim G`, then `X = colim F`.
-/
noncomputable
/-
**CategoryTheory.Limits.isColimitOfIsPushoutOfIsConnected** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfIsPushoutOfIsConnected {I C : Type*} [Category* I] [IsConnected
 I] [Category* C] {F G : I ⥤ C} (α : F ⟶ G) (cF : Cocone F) (cG : Cocone G) (f :
 cF ⟶ (Cocone.precompose α).obj cG) (hf : forall i, IsPushout (cF.ι.app i) (α.ap
p i) f.hom (cG.ι.app i)) (hcF : IsColimit cF) : IsColimit cG where desc s
参数：α : F ⟶ G；cF : Cocone F；cG : Cocone G；f : cF ⟶ (Cocone.precompose α).obj cG；h
f : forall i, IsPushout (cF.ι.app i) (α.app i) f.hom (cG.ι.app i)；hcF : IsColimi
t cF。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
-/
def isColimitOfIsPushoutOfIsConnected
    {I C : Type*} [Category* I] [IsConnected I] [Category* C] {F G : I ⥤ C}
    (α : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (f : cF ⟶ (Cocone.precompose α).obj cG)
    (hf : ∀ i, IsPushout (cF.ι.app i) (α.app i) f.hom (cG.ι.app i))
    (hcF : IsColimit cF) : IsColimit cG where
  desc s := (hf (Classical.arbitrary _)).desc
    (hcF.desc ((Cocone.precompose α).obj s)) (s.ι.app (Classical.arbitrary _)) (by simp)
  fac s j := by
    let f (i : _) : cG.pt ⟶ s.pt :=
      (hf i).desc (hcF.desc ((Cocone.precompose α).obj s)) (s.ι.app i) (by simp)
    have (i j : _) : f i = f j := by
      refine constant_of_preserves_morphisms f (fun j₁ j₂ g ↦ ?_) i j
      refine (hf j₁).hom_ext (by simp [f]) ?_
      rw [IsPushout.inr_desc, ← cG.w g, Category.assoc, IsPushout.inr_desc, Cocone.w]
    change _ ≫ f _ = _
    rw [this _ j]
    simp [f]
  uniq s g hg := (hf (Classical.arbitrary _)).hom_ext (hcF.hom_ext <| by simp [hg]) (by simp [hg])

end CategoryTheory.Limits

