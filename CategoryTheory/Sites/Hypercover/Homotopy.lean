/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The category of `1`-hypercovers up to homotopy

In this file we define the category of `1`-hypercovers up to homotopy. This is the category of
`1`-hypercovers, but where morphisms are considered up to existence of a homotopy.

## Main definitions

- `CategoryTheory.PreOneHypercover.Homotopy`: A homotopy of refinements `E ⟶ F` is a family of
  morphisms `Xᵢ ⟶ Yₐ` where `Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`.
- `CategoryTheory.GrothendieckTopology.HOneHypercover`: The category of `1`-hypercovers
  with respect to a Grothendieck topology and morphisms up to homotopy.

## Main results

- `CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks`: The
  category of `1`-hypercovers up to homotopy is cofiltered if `C` has pullbacks.
-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}

/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
structure Homotopy
  parameters: (f g : E.Hom F)
  axioms and operations (4):
    - H((i : E.I₀)) : F.I₁ (f.s₀ i) (g.s₀ i)
    - a((i : E.I₀)) : E.X i ⟶ F.Y (H i)
    - wl((i : E.I₀)) : a i ≫ F.p₁ (H i) = f.h₀ i
    - wr((i : E.I₀)) : a i ≫ F.p₂ (H i) = g.h₀ i

中文:
结构 Homotopy
  参数: (f g : E.Hom F)
  公理与运算 (4 个):
    - H((i : E.I₀)) : F.I₁ (f.s₀ i) (g.s₀ i)
    - a((i : E.I₀)) : E.X i ⟶ F.Y (H i)
    - wl((i : E.I₀)) : a i ≫ F.p₁ (H i) = f.h₀ i
    - wr((i : E.I₀)) : a i ≫ F.p₂ (H i) = g.h₀ i

Depends on / 依赖: Homotopy, Homotopy.wl, Homotopy.wr
-/
structure Homotopy (f g : E.Hom F) where
  /-- The index map sending `i : E.I₀` to `a` above `(f(i), g(i))`. -/
  H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i)
  /-- The morphism `Xᵢ ⟶ Yₐ`. -/
  a (i : E.I₀) : E.X i ⟶ F.Y (H i)
  wl (i : E.I₀) : a i ≫ F.p₁ (H i) = f.h₀ i
  wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i

attribute [reassoc (attr := simp)] Homotopy.wl Homotopy.wr

section

variable {A : Type*} [Category* A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Homotopy.mapMultiforkOfIsLimit_eq` / 引理 `Homotopy.mapMultiforkOfIsLimit_eq`

English:
lemma Homotopy.mapMultiforkOfIsLimit_eq
  proof: by
  refine Multifork.IsLimit.hom_ext hc fun a => ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.

中文:
引理 Homotopy.mapMultiforkOfIsLimit_eq
  证明: by
  refine Multifork.IsLimit.hom_ext hc fun a => ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.

Depends on / 依赖: H.wl, H.wr, Homotopy, Homotopy.wl, Homotopy.wr, IsLimit, Multifork, Multifork.IsLimit.hom_ext, condition, d.condition, hom_ext, multicospanIndex_fst, multicospanIndex_left, multicospanIndex_right, multicospanIndex_snd, multicospanShape_fst, multicospanShape_snd, reassoc_of
-/
lemma Homotopy.mapMultiforkOfIsLimit_eq
    {E F : PreOneHypercover.{w} S} {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  refine Multifork.IsLimit.hom_ext hc fun a => ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.wr, ← H.wl, ← H.wr, reassoc_of% heq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Homotopy.isLimitMultifork` / `Homotopy.isLimitMultifork` 的定义

English:
definition Homotopy.isLimitMultifork
  signature: (f : E.Hom F) (g : F.Hom E) (hgf : Homotopy (g.comp f) (.id F))
  body: by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a => t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁]; rw [← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
   

中文:
定义 Homotopy.isLimitMultifork
  签名: (f : E.Hom F) (g : F.Hom E) (hgf : Homotopy (g.comp f) (.id F))
  定义体: by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a => t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁]; rw [← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
   

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, G.map, IsLimit, Multifork, Multifork.IsLimit.lift, Multifork.IsLimit.mk, condition, condition_assoc, hgf.H, hgf.wl, map_comp, multicospanIndex_left, multicospanShape_L, op_comp, t.condition, t.condition_assoc
-/
def Homotopy.isLimitMultifork (f : E.Hom F) (g : F.Hom E) (hgf : Homotopy (g.comp f) (.id F))
    {G : Cᵒᵖ ⥤ A} (hE : IsLimit (E.multifork G)) :
    IsLimit (F.multifork G) := by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a => t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁]; rw [← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
    exact t.condition_assoc ⟨(f.s₀ b.1.1, f.s₀ b.1.2), f.s₁ b.2⟩ _
  · intro t i
    simp only [multicospanIndex_left, multicospanShape_L, multifork_ι]
    have h1 := hgf.wl i
    have h2 := t.condition ⟨⟨_, _⟩, hgf.H i⟩
    dsimp at h1 h2
    rw [← g.w₀]; rw [op_comp]; rw [Functor.map_comp]; rw [← E.multifork_ι]; rw [Multifork.IsLimit.fac_assoc]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← h1]; rw [op_comp]; rw [Functor.map_comp]; rw [reassoc_of% h2]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hgf.wr i]
    simp
  · intro t m hm
    refine Multifork.IsLimit.hom_ext hE fun i => ?_
    rw [Multifork.IsLimit.fac]; rw [multifork_ι]; rw [← f.w₀]; rw [op_comp]; rw [Functor.map_comp]; rw [← F.multifork_ι]; rw [reassoc_of% hm]

/--
Definition of `Homotopy.isLimitMultiforkEquiv` / `Homotopy.isLimitMultiforkEquiv` 的定义

English:
definition Homotopy.isLimitMultiforkEquiv
  signature: (f : E.Hom F) (g : F.Hom E)
  body: hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 Homotopy.isLimitMultiforkEquiv
  签名: (f : E.Hom F) (g : F.Hom E)
  定义体: hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: hgf.isLimitMultifork, isLimitMultifork
-/
def Homotopy.isLimitMultiforkEquiv (f : E.Hom F) (g : F.Hom E)
    (hfg : Homotopy (f.comp g) (.id E)) (hgf : Homotopy (g.comp f) (.id F)) {G : Cᵒᵖ ⥤ A} :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) where
  toFun h := hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end

variable [Limits.HasPullbacks C] (f g : E.Hom F)

/-- (Implementation): The covering object of `cylinder f g`. -/
noncomputable
/--
Definition of `cylinderX` / `cylinderX` 的定义

English:
abbreviation cylinderX
  signature: {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i))
  body: pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

中文:
缩写 cylinderX
  签名: {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i))
  定义体: pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

Depends on / 依赖: F.toPullback, pullback, pullback.lift, toPullback
-/
abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

/-- (Implementation): The structure morphisms of the covering objects of `cylinder f g`. -/
noncomputable
/--
Definition of `cylinderf` / `cylinderf` 的定义

English:
abbreviation cylinderf
  signature: {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i))
  body: pullback.fst _ _ ≫ E.f _

中文:
缩写 cylinderf
  签名: {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i))
  定义体: pullback.fst _ _ ≫ E.f _

Depends on / 依赖: pullback, pullback.fst
-/
abbrev cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S :=
  pullback.fst _ _ ≫ E.f _

/-- Given two refinement morphisms `f, g : E ⟶ F`, this is a (pre-)`1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
This is a `1`-hypercover, if `E` and `F` are (see `OneHypercover.cylinder`). -/
@[simps]
/--
Definition of `cylinder` / `cylinder` 的定义

English:
definition cylinder
  signature: (f g : E.Hom F)
  body: Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by

中文:
定义 cylinder
  签名: (f g : E.Hom F)
  定义体: Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by
-/
noncomputable def cylinder (f g : E.Hom F) : PreOneHypercover.{max w w'} S where
  I₀ := Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by simp))
      (pullback.lift _ _ (E.w k.down))
  p₁ {p q} k := pullback.fst _ _ ≫ pullback.fst _ _
  p₂ {p q} k := pullback.fst _ _ ≫ pullback.snd _ _
  w {_ _} k := by simp [pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `toPullback_cylinder` / 引理 `toPullback_cylinder`

English:
lemma toPullback_cylinder
  given: {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j)
  proof: by
  apply pullback.hom_ext <;> simp [toPullback]

中文:
引理 toPullback_cylinder
  条件: {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j)
  证明: by
  apply pullback.hom_ext <;> simp [toPullback]

Depends on / 依赖: hom_ext, pullback, pullback.hom_ext, toPullback
-/
lemma toPullback_cylinder {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j) :
    (cylinder f g).toPullback k = pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp [toPullback]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sieve₀_cylinder` / 引理 `sieve₀_cylinder`

English:
lemma sieve₀_cylinder
  proof: by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.

中文:
引理 sieve₀_cylinder
  证明: by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.sieve, Presieve, Presieve.ofArrows.mk, Sieve.downward_closed, Sieve.generate_le_iff, Sieve.ofArrows_mk, Sieve.pullback_apply, condition, cylinder, downward_closed, generate_le_iff, le_antisymm, ofArrows, ofArrows_mk, pullback, pullback.condition, pullback.lift, pullback_apply
-/
lemma sieve₀_cylinder :
    (cylinder f g).sieve₀ =
      Sieve.generate
        (Presieve.bindOfArrows _ E.f <| fun i =>
          (Sieve.pullback (pullback.lift (f.h₀ _) (g.h₀ _) (by simp))
            (F.sieve₁' _ _)).arrows) := by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.generate_le_iff, PreZeroHypercover.sieve₀]
    rintro Z u ⟨i, v, ⟨W, o, o', ⟨j⟩, hoo'⟩⟩
    exact ⟨_, pullback.lift v o hoo'.symm, (cylinder f g).f ⟨i, j⟩, Presieve.ofArrows.mk _,
      by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sieve₁'_cylinder` / 引理 `sieve₁'_cylinder`

English:
lemma sieve₁'_cylinder
  given: (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i))
  proof: by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Si

中文:
引理 sieve₁'_cylinder
  条件: (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i))
  证明: by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Si

Depends on / 依赖: E.toPullback, Presieve, Presieve.ofArrows.mk, Sieve.generate_le_iff, Sieve.ofArro, Sieve.ofArrows, Sieve.pullbackArrows_comm, condition, convert, cylinder, cylinder_Y, cylinder_f, downward_closed, generate_le_iff, k.down, le_antisymm, ofArro, ofArrows, pullback, pullback.condition
-/
lemma sieve₁'_cylinder (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)) :
    (cylinder f g).sieve₁' i j =
      Sieve.pullback
        (pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp) (by simp))
        (E.sieve₁' i.1 j.1) := by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Sieve.ofArrows, ← Sieve.pullbackArrows_comm, Sieve.generate_le_iff]
    rintro Z u ⟨W, v, ⟨k⟩⟩
    simp_rw [← pullbackSymmetry_inv_comp_fst]
    apply (((cylinder f g).sieve₁' i j)).downward_closed
    rw [sieve₁']
    convert! Sieve.ofArrows_mk _ _ (ULift.up k)
    simp [toPullback_cylinder f g ⟨k⟩]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): The refinement morphism `cylinder f g ⟶ E`. -/
@[simps]
/--
Definition of `cylinderHom` / `cylinderHom` 的定义

English:
definition cylinderHom
  signature: : (cylinder f g).Hom E where
  body: p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.

中文:
定义 cylinderHom
  签名: : (cylinder f g).Hom E where
  定义体: p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.
-/
noncomputable def cylinderHom : (cylinder f g).Hom E where
  s₀ p := p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.snd _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₀ := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cylinderHomotopy` / `cylinderHomotopy` 的定义

English:
definition cylinderHomotopy
  signature: :
  body: p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd 

中文:
定义 cylinderHomotopy
  签名: :
  定义体: p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd 
-/
noncomputable def cylinderHomotopy :
    Homotopy ((cylinderHom f g).comp f) ((cylinderHom f g).comp g) where
  H p := p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd (F.f _) (F.f _) := by simp
    dsimp only [cylinder_X, Hom.comp_s₀, cylinder_I₀, Function.comp_apply, cylinderHom_s₀,
      Hom.comp_h₀, cylinderHom_h₀]
    nth_rw 3 [this]
    rw [pullback.condition_assoc]
    simp

/--
lemma `exists_nonempty_homotopy` / 引理 `exists_nonempty_homotopy`

English:
lemma exists_nonempty_homotopy
  given: (f g : E.Hom F)
  proof: ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

中文:
引理 exists_nonempty_homotopy
  条件: (f g : E.Hom F)
  证明: ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

Depends on / 依赖: PreOneHypercover, PreOneHypercover.cylinderHom, cylinder, cylinderHom, cylinderHomotopy
-/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    exists (W : PreOneHypercover.{max w w'} S) (h : W.Hom E),
      Nonempty (Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

end PreOneHypercover

namespace GrothendieckTopology

open PreOneHypercover OneHypercover

variable {J : GrothendieckTopology C}

namespace OneHypercover

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}
variable [HasPullbacks C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given two refinement morphism `f, g : E ⟶ F`, this is a `1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy. -/
@[simps! toPreOneHypercover]
/--
Definition of `cylinder` / `cylinder` 的定义

English:
definition cylinder
  signature: (f g : E.Hom F)
  body: mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i => ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j => by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pu

中文:
定义 cylinder
  签名: (f g : E.Hom F)
  定义体: mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i => ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j => by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pu

Depends on / 依赖: E.mem, J.bindOfArrows, J.pullback_stable, PreOneHypercover, PreOneHypercover.cylinder, PreOneHypercover.sieve, Sieve.generate_sieve, _cylinder, bindOfArrows, cylinder, generate_sieve, pullback_stable
-/
noncomputable def cylinder (f g : E.Hom F) : J.OneHypercover S :=
  mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i => ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j => by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pullback_stable _ (mem_sieve₁' E _ _))

/--
lemma `exists_nonempty_homotopy` / 引理 `exists_nonempty_homotopy`

English:
lemma exists_nonempty_homotopy
  given: (f g : E.Hom F)
  proof: ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

中文:
引理 exists_nonempty_homotopy
  条件: (f g : E.Hom F)
  证明: ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

Depends on / 依赖: PreOneHypercover, PreOneHypercover.cylinderHom, PreOneHypercover.cylinderHomotopy, cylinder, cylinderHom, cylinderHomotopy
-/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    exists (W : OneHypercover.{max w w'} J S) (h : W.Hom E),
      Nonempty (PreOneHypercover.Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

end OneHypercover

variable (J S)

/--
Definition of `OneHypercover.homotopicRel` / `OneHypercover.homotopicRel` 的定义

English:
definition OneHypercover.homotopicRel
  signature: : HomRel (J.OneHypercover S)
  body: fun _ _ f g => Nonempty (PreOneHypercover.Homotopy f g)

中文:
定义 OneHypercover.homotopicRel
  签名: : HomRel (J.OneHypercover S)
  定义体: fun _ _ f g => Nonempty (PreOneHypercover.Homotopy f g)

Depends on / 依赖: Homotopy, Nonempty, PreOneHypercover, PreOneHypercover.Homotopy
-/
def OneHypercover.homotopicRel : HomRel (J.OneHypercover S) :=
  fun _ _ f g => Nonempty (PreOneHypercover.Homotopy f g)

/--
Definition of `HOneHypercover` / `HOneHypercover` 的定义

English:
abbreviation HOneHypercover
  signature: (S : C)
  body: Quotient (OneHypercover.homotopicRel J S)

中文:
缩写 HOneHypercover
  签名: (S : C)
  定义体: Quotient (OneHypercover.homotopicRel J S)

Depends on / 依赖: OneHypercover, OneHypercover.homotopicRel, Quotient, homotopicRel
-/
abbrev HOneHypercover (S : C) := Quotient (OneHypercover.homotopicRel J S)

/--
Definition of `OneHypercover.toHOneHypercover` / `OneHypercover.toHOneHypercover` 的定义

English:
abbreviation OneHypercover.toHOneHypercover
  signature: (S : C)
  body: Quotient.functor _

中文:
缩写 OneHypercover.toHOneHypercover
  签名: (S : C)
  定义体: Quotient.functor _

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
abbrev OneHypercover.toHOneHypercover (S : C) : J.OneHypercover S ⥤ J.HOneHypercover S :=
  Quotient.functor _

/--
lemma `_root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map` / 引理 `_root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map`

English:
lemma _root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map
  statement: {S : C} {E F : J.OneHypercover S}
  proof: Quotient.sound _ ⟨H⟩

中文:
引理 _root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map
  结论: {S : C} {E F : J.OneHypercover S}
  证明: Quotient.sound _ ⟨H⟩

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma _root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map {S : C} {E F : J.OneHypercover S}
    {f g : E ⟶ F} (H : Homotopy f g) :
    (toHOneHypercover J S).map f = (toHOneHypercover J S).map g :=
  Quotient.sound _ ⟨H⟩

namespace HOneHypercover

variable {S : C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (J.HOneHypercover S)
  body: ⟨⟨Nonempty.some inferInstance⟩⟩

中文:
实例 :
  签名: Nonempty (J.HOneHypercover S)
  定义体: ⟨⟨Nonempty.some inferInstance⟩⟩

Depends on / 依赖: Nonempty, Nonempty.some
-/
instance : Nonempty (J.HOneHypercover S) := ⟨⟨Nonempty.some inferInstance⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isCofiltered_of_hasPullbacks` / 实例 `isCofiltered_of_hasPullbacks`

English:
instance isCofiltered_of_hasPullbacks
  signature: [HasPullbacks C]
  body: ⟨⟨E.1.inter F.1⟩, Quot.mk _ (PreOneHypercover.interFst _ _),
      Quot.mk _ (PreOneHypercover.interSnd _ _), ⟨⟩⟩
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    

中文:
实例 isCofiltered_of_hasPullbacks
  签名: [HasPullbacks C]
  定义体: ⟨⟨E.1.inter F.1⟩, Quot.mk _ (PreOneHypercover.interFst _ _),
      Quot.mk _ (PreOneHypercover.interSnd _ _), ⟨⟩⟩
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    

Depends on / 依赖: Functor, Functor.map_comp, H.map_eq_map, OneHypercover, OneHypercover.exists_nonempty_homotopy, PreOneHypercover, PreOneHypercover.interFst, PreOneHypercover.interSnd, Quot.mk, cone_maps, exists_nonempty_homotopy, interFst, interSnd, map_comp, map_eq_map, map_surjective, toHOneHypercover
-/
instance isCofiltered_of_hasPullbacks [HasPullbacks C] : IsCofiltered (J.HOneHypercover S) where
  cone_objs {E F} :=
    ⟨⟨E.1.inter F.1⟩, Quot.mk _ (PreOneHypercover.interFst _ _),
      Quot.mk _ (PreOneHypercover.interSnd _ _), ⟨⟩⟩
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    obtain ⟨W, h, ⟨H⟩⟩ := OneHypercover.exists_nonempty_homotopy f g
    use (toHOneHypercover J S).obj W, (toHOneHypercover J S).map h
    rw [← Functor.map_comp]; rw [← Functor.map_comp]
    exact H.map_eq_map

end HOneHypercover

end GrothendieckTopology

end CategoryTheory
