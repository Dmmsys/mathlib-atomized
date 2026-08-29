/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Batteries.Tactic.Congr

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The main structures defined in this file is
* `IsLimit c`, for `c : Cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,

See also `CategoryTheory.Limits.HasLimits` which further builds:
* `LimitCone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `HasLimit F`, asserting the mere existence of some limit cone for `F`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C]
variable {F : J ⥤ C}

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`. -/
@[stacks 002E]
/--
Definition of `IsLimit` / `IsLimit` 的定义

English:
structure IsLimit
  parameters: (t : Cone F)
  axioms and operations (3):
    - lift : forall s : Cone F, s.pt ⟶ t.pt
    - fac : forall (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j  [default: by cat_disch]
    - uniq : forall (s : Cone F) (m : s.pt ⟶ t.pt) (_ : forall j : J, m ≫ t.π.app j = s.π.app j), m = lift s  [default: by cat_disch]

中文:
结构 是极限
  参数: (t : 锥 F)
  公理与运算 (3 个):
    - lift : 对任意 s : 锥 F, s.pt ⟶ t.pt
    - fac : 对任意 (s : 锥 F) (j : J), lift s ≫ t.π.app j = s.π.app j  [默认: by cat_disch]
    - uniq : 对任意 (s : 锥 F) (m : s.pt ⟶ t.pt) (_ : 对任意 j : J, m ≫ t.π.app j = s.π.app j), m = lift s  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : forall s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : forall (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch
  /-- It is the unique such map to do this -/
  uniq : forall (s : Cone F) (m : s.pt ⟶ t.pt) (_ : forall j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by
    cat_disch

/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`. -/
@[stacks 002F, to_dual]
/--
Definition of `IsColimit` / `IsColimit` 的定义

English:
structure IsColimit
  parameters: (t : Cocone F)
  axioms and operations (3):
    - desc : forall s : Cocone F, t.pt ⟶ s.pt
    - fac : forall (s : Cocone F) (j : J), dsimp% t.ι.app j ≫ desc s = s.ι.app j  [default: by cat_disch]
    - uniq : dsimp% forall (s : Cocone F) (m : t.pt ⟶ s.pt) (_ : forall j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s  [default: by cat_disch]

中文:
结构 是余极限
  参数: (t : 余锥 F)
  公理与运算 (3 个):
    - desc : 对任意 s : 余锥 F, t.pt ⟶ s.pt
    - fac : 对任意 (s : 余锥 F) (j : J), dsimp% t.ι.app j ≫ desc s = s.ι.app j  [默认: by cat_disch]
    - uniq : dsimp% 对任意 (s : 余锥 F) (m : t.pt ⟶ s.pt) (_ : 对任意 j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsColimit (t : Cocone F) where
  /-- `t.pt` maps to all other cocone covertices -/
  desc : forall s : Cocone F, t.pt ⟶ s.pt
  /-- The map `desc` makes the diagram with the natural transformations commute -/
  fac : forall (s : Cocone F) (j : J), dsimp% t.ι.app j ≫ desc s = s.ι.app j := by cat_disch
  /-- `desc` is the unique such map -/
  uniq : dsimp%
    forall (s : Cocone F) (m : t.pt ⟶ s.pt) (_ : forall j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s := by
    cat_disch

attribute [reassoc (attr := simp)] IsLimit.fac IsColimit.fac

to_dual_name_hint Lift Desc, Left Right

namespace IsLimit

@[to_dual]
/--
Instance `subsingleton` / 实例 `subsingleton`

English:
instance subsingleton
  signature: {t : Cone F}
  body: ⟨by intro P Q; cases P; cases Q; congr; cat_disch⟩

中文:
实例 subsingleton
  签名: {t : 锥 F}
  定义体: ⟨by intro P Q; cases P; cases Q; congr; cat_disch⟩

Depends on / 依赖: cat_disch
-/
instance subsingleton {t : Cone F} : Subsingleton (IsLimit t) :=
  ⟨by intro P Q; cases P; cases Q; congr; cat_disch⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
@[implicit_reducible, to_dual (reorder := s P t)
/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {F G : J ⥤ C} (s : Cone F) {t : Cone G} (P : IsLimit t) (α : F ⟶ G)
  body: P.lift ((Cone.postcompose α).obj s)

@[to_dual (attr := reassoc (attr := simp)) (reorder := c hd d) ι_map]

中文:
定义 map
  签名: {F G : J ⥤ C} (s : 锥 F) {t : 锥 G} (P : 是极限 t) (α : F ⟶ G)
  定义体: P.lift ((Cone.postcompose α).obj s)

@[to_dual (attr := reassoc (attr := simp)) (reorder := c hd d) ι_map]

Depends on / 依赖: Cone.postcompose, P.lift, postcompose
-/
def map {F G : J ⥤ C} (s : Cone F) {t : Cone G} (P : IsLimit t) (α : F ⟶ G) : s.pt ⟶ t.pt :=
  P.lift ((Cone.postcompose α).obj s)

@[to_dual (attr := reassoc (attr := simp)) (reorder := c hd d) ι_map]
/--
theorem `map_π` / 定理 `map_π`

English:
theorem map_π
  given: {F G : J ⥤ C} (c : Cone F) {d : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J)
  proof: fac _ _ _

@[to_dual (attr := simp)]

中文:
定理 map_π
  条件: {F G : J ⥤ C} (c : 锥 F) {d : 锥 G} (hd : 是极限 d) (α : F ⟶ G) (j : J)
  证明: fac _ _ _

@[to_dual (attr := simp)]
-/
theorem map_π {F G : J ⥤ C} (c : Cone F) {d : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) :
    hd.map c α ≫ d.π.app j = c.π.app j ≫ α.app j :=
  fac _ _ _

@[to_dual (attr := simp)]
/--
theorem `lift_self` / 定理 `lift_self`

English:
theorem lift_self
  given: {c : Cone F} (t : IsLimit c)
  statement: t.lift c = 𝟙 c.pt
  proof: (t.uniq _ _ fun _ => id_comp _).symm

中文:
定理 lift_self
  条件: {c : 锥 F} (t : 是极限 c)
  结论: t.lift c = 𝟙 c.pt
  证明: (t.uniq _ _ fun _ => id_comp _).symm

Depends on / 依赖: id_comp, t.uniq
-/
theorem lift_self {c : Cone F} (t : IsLimit c) : t.lift c = 𝟙 c.pt :=
  (t.uniq _ _ fun _ => id_comp _).symm

-- Repackaging the definition in terms of cone morphisms.
/-- The universal morphism from any other cone to a limit cone. -/
@[to_dual (attr := simps)
/-- The universal morphism from a colimit cocone to any other cocone. -/]
/--
Definition of `liftConeMorphism` / `liftConeMorphism` 的定义

English:
definition liftConeMorphism
  signature: {t : Cone F} (h : IsLimit t) (s : Cone F)
  body: h.lift s

@[to_dual]

中文:
定义 liftConeMorphism
  签名: {t : 锥 F} (h : 是极限 t) (s : 锥 F)
  定义体: h.lift s

@[to_dual]

Depends on / 依赖: h.lift
-/
def liftConeMorphism {t : Cone F} (h : IsLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

@[to_dual]
/--
theorem `uniq_cone_morphism` / 定理 `uniq_cone_morphism`

English:
theorem uniq_cone_morphism
  given: {s t : Cone F} (h : IsLimit t) {f f' : s ⟶ t}
  statement: f = f'
  proof: have : forall {g : s ⟶ t}, g = h.liftConeMorphism s := by
    intro g; apply ConeMorphism.ext; exact h.uniq _ _ g.w
  this.trans this.symm

中文:
定理 uniq_cone_morphism
  条件: {s t : 锥 F} (h : 是极限 t) {f f' : s ⟶ t}
  结论: f = f'
  证明: have : forall {g : s ⟶ t}, g = h.liftConeMorphism s := by
    intro g; apply ConeMorphism.ext; exact h.uniq _ _ g.w
  this.trans this.symm

Depends on / 依赖: ConeMorphism, ConeMorphism.ext, h.liftConeMorphism, h.uniq, liftConeMorphism, this.symm, this.trans
-/
theorem uniq_cone_morphism {s t : Cone F} (h : IsLimit t) {f f' : s ⟶ t} : f = f' :=
  have : forall {g : s ⟶ t}, g = h.liftConeMorphism s := by
    intro g; apply ConeMorphism.ext; exact h.uniq _ _ g.w
  this.trans this.symm

/-- Restating the definition of a limit cone in terms of the ∃! operator. -/
@[to_dual /-- Restating the definition of a colimit cocone in terms of the ∃! operator. -/]
/--
theorem `existsUnique` / 定理 `existsUnique`

English:
theorem existsUnique
  given: {t : Cone F} (h : IsLimit t) (s : Cone F)
  proof: ⟨h.lift s, h.fac s, h.uniq s⟩

中文:
定理 存在Unique
  条件: {t : 锥 F} (h : 是极限 t) (s : 锥 F)
  证明: ⟨h.lift s, h.fac s, h.uniq s⟩

Depends on / 依赖: h.fac, h.lift, h.uniq
-/
theorem existsUnique {t : Cone F} (h : IsLimit t) (s : Cone F) :
    exists! l : s.pt ⟶ t.pt, forall j, l ≫ t.π.app j = s.π.app j :=
  ⟨h.lift s, h.fac s, h.uniq s⟩

/-- Noncomputably make a limit cone from the existence of unique factorizations. -/
@[to_dual /-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/]
/--
Definition of `ofExistsUnique` / `ofExistsUnique` 的定义

English:
definition ofExistsUnique
  signature: {t : Cone F}
  body: by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩

中文:
定义 ofExistsUnique
  签名: {t : 锥 F}
  定义体: by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩
-/
def ofExistsUnique {t : Cone F}
    (ht : forall s : Cone F, exists! l : s.pt ⟶ t.pt, forall j, l ≫ t.π.app j = s.π.app j) : IsLimit t := by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩

/-- Alternative constructor for `isLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[to_dual (attr := simps)
/-- Alternative constructor for `IsColimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/]
/--
Definition of `mkConeMorphism` / `mkConeMorphism` 的定义

English:
definition mkConeMorphism
  signature: {t : Cone F} (lift : forall s : Cone F, s ⟶ t)
  body: (lift s).hom
  uniq s m w :=
    have : ConeMorphism.mk m w = lift s := by apply uniq
    congrArg ConeMorphism.hom this

中文:
定义 mkConeMorphism
  签名: {t : 锥 F} (lift : 对任意 s : 锥 F, s ⟶ t)
  定义体: (lift s).hom
  uniq s m w :=
    have : ConeMorphism.mk m w = lift s := by apply uniq
    congrArg ConeMorphism.hom this
-/
def mkConeMorphism {t : Cone F} (lift : forall s : Cone F, s ⟶ t)
    (uniq : forall (s : Cone F) (m : s ⟶ t), m = lift s) : IsLimit t where
  lift s := (lift s).hom
  uniq s m w :=
    have : ConeMorphism.mk m w = lift s := by apply uniq
    congrArg ConeMorphism.hom this

set_option linter.translate.warnInvalid false in
/-- Limit cones on `F` are unique up to isomorphism. -/
@[to_dual (attr := simps) /-- Colimit cocones on `F` are unique up to isomorphism. -/]
/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: {s t : Cone F} (P : IsLimit s) (Q : IsLimit t)
  body: Q.liftConeMorphism s
  inv := P.liftConeMorphism t
  hom_inv_id := P.uniq_cone_morphism
  inv_hom_id := Q.uniq_cone_morphism

中文:
定义 uniqueUpToIso
  签名: {s t : 锥 F} (P : 是极限 s) (Q : 是极限 t)
  定义体: Q.liftConeMorphism s
  inv := P.liftConeMorphism t
  hom_inv_id := P.uniq_cone_morphism
  inv_hom_id := Q.uniq_cone_morphism

Depends on / 依赖: Localization, Localization.inverts, Q.liftConeMorphism, inverts, liftConeMorphism, z.hs
-/
def uniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s ≅ t where
  hom := Q.liftConeMorphism s
  inv := P.liftConeMorphism t
  hom_inv_id := P.uniq_cone_morphism
  inv_hom_id := Q.uniq_cone_morphism

attribute [to_dual existing uniqueUpToIso_inv] uniqueUpToIso_hom
attribute [to_dual existing uniqueUpToIso_hom] uniqueUpToIso_inv

/-- Any cone morphism between limit cones is an isomorphism. -/
@[to_dual (reorder := P Q) /-- Any cocone morphism between colimit cocones is an isomorphism. -/]
/--
theorem `hom_isIso` / 定理 `hom_isIso`

English:
theorem hom_isIso
  given: {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (f : s ⟶ t)
  statement: IsIso f
  proof: ⟨⟨P.liftConeMorphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

中文:
定理 hom_isIso
  条件: {s t : 锥 F} (P : 是极限 s) (Q : 是极限 t) (f : s ⟶ t)
  结论: 是同构 f
  证明: ⟨⟨P.liftConeMorphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

Depends on / 依赖: Localization, Localization.inverts, P.liftConeMorphism, P.uniq_cone_morphism, Q.uniq_cone_morphism, inverts, liftConeMorphism, uniq_cone_morphism, z.hs
-/
theorem hom_isIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (f : s ⟶ t) : IsIso f :=
  ⟨⟨P.liftConeMorphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

/-- Limits of `F` are unique up to isomorphism. -/
@[to_dual /-- Colimits of `F` are unique up to isomorphism. -/]
/--
Definition of `conePointUniqueUpToIso` / `conePointUniqueUpToIso` 的定义

English:
definition conePointUniqueUpToIso
  signature: {s t : Cone F} (P : IsLimit s) (Q : IsLimit t)
  body: (Cone.forget F).mapIso (uniqueUpToIso P Q)

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]

中文:
定义 conePointUniqueUpToIso
  签名: {s t : 锥 F} (P : 是极限 s) (Q : 是极限 t)
  定义体: (Cone.forget F).mapIso (uniqueUpToIso P Q)

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]

Depends on / 依赖: Cone.forget, Localization, Localization.inverts, forget, inverts, mapIso, uniqueUpToIso, z.hs
-/
def conePointUniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s.pt ≅ t.pt :=
  (Cone.forget F).mapIso (uniqueUpToIso P Q)

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
/--
theorem `conePointUniqueUpToIso_hom_comp` / 定理 `conePointUniqueUpToIso_hom_comp`

English:
theorem conePointUniqueUpToIso_hom_comp
  given: {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J)
  proof: (uniqueUpToIso P Q).hom.w _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]

中文:
定理 conePointUniqueUpToIso_hom_comp
  条件: {s t : 锥 F} (P : 是极限 s) (Q : 是极限 t) (j : J)
  证明: (uniqueUpToIso P Q).hom.w _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]

Depends on / 依赖: hom.w, uniqueUpToIso
-/
theorem conePointUniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.app j :=
  (uniqueUpToIso P Q).hom.w _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]
/--
theorem `conePointUniqueUpToIso_inv_comp` / 定理 `conePointUniqueUpToIso_inv_comp`

English:
theorem conePointUniqueUpToIso_inv_comp
  given: {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J)
  proof: (uniqueUpToIso P Q).inv.w _

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_inv_desc]

中文:
定理 conePointUniqueUpToIso_inv_comp
  条件: {s t : 锥 F} (P : 是极限 s) (Q : 是极限 t) (j : J)
  证明: (uniqueUpToIso P Q).inv.w _

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_inv_desc]

Depends on / 依赖: inv.w, uniqueUpToIso
-/
theorem conePointUniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.app j :=
  (uniqueUpToIso P Q).inv.w _

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_inv_desc]
/--
theorem `lift_comp_conePointUniqueUpToIso_hom` / 定理 `lift_comp_conePointUniqueUpToIso_hom`

English:
theorem lift_comp_conePointUniqueUpToIso_hom
  given: {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t)
  proof: Q.uniq _ _ (by simp)

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_hom_desc]

中文:
定理 lift_comp_conePointUniqueUpToIso_hom
  条件: {r s t : 锥 F} (P : 是极限 s) (Q : 是极限 t)
  证明: Q.uniq _ _ (by simp)

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_hom_desc]

Depends on / 依赖: Q.uniq
-/
theorem lift_comp_conePointUniqueUpToIso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    P.lift r ≫ (conePointUniqueUpToIso P Q).hom = Q.lift r :=
  Q.uniq _ _ (by simp)

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_hom_desc]
/--
theorem `lift_comp_conePointUniqueUpToIso_inv` / 定理 `lift_comp_conePointUniqueUpToIso_inv`

English:
theorem lift_comp_conePointUniqueUpToIso_inv
  given: {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t)
  proof: P.uniq _ _ (by simp)

中文:
定理 lift_comp_conePointUniqueUpToIso_inv
  条件: {r s t : 锥 F} (P : 是极限 s) (Q : 是极限 t)
  证明: P.uniq _ _ (by simp)

Depends on / 依赖: P.uniq
-/
theorem lift_comp_conePointUniqueUpToIso_inv {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    Q.lift r ≫ (conePointUniqueUpToIso P Q).inv = P.lift r :=
  P.uniq _ _ (by simp)

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
@[to_dual
/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/]
/--
Definition of `ofIsoLimit` / `ofIsoLimit` 的定义

English:
definition ofIsoLimit
  signature: {r t : Cone F} (P : IsLimit r) (i : r ≅ t)
  body: IsLimit.mkConeMorphism (fun s => P.liftConeMorphism s ≫ i.hom) fun s m => by
    rw [← i.comp_inv_eq]; apply P.uniq_cone_morphism

@[to_dual (attr := simp)]

中文:
定义 ofIsoLimit
  签名: {r t : 锥 F} (P : 是极限 r) (i : r ≅ t)
  定义体: IsLimit.mkConeMorphism (fun s => P.liftConeMorphism s ≫ i.hom) fun s m => by
    rw [← i.comp_inv_eq]; apply P.uniq_cone_morphism

@[to_dual (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.mkConeMorphism, P.liftConeMorphism, P.uniq_cone_morphism, comp_inv_eq, i.comp_inv_eq, i.hom, liftConeMorphism, mkConeMorphism, uniq_cone_morphism
-/
def ofIsoLimit {r t : Cone F} (P : IsLimit r) (i : r ≅ t) : IsLimit t :=
  IsLimit.mkConeMorphism (fun s => P.liftConeMorphism s ≫ i.hom) fun s m => by
    rw [← i.comp_inv_eq]; apply P.uniq_cone_morphism

@[to_dual (attr := simp)]
/--
theorem `ofIsoLimit_lift` / 定理 `ofIsoLimit_lift`

English:
theorem ofIsoLimit_lift
  given: {r t : Cone F} (P : IsLimit r) (i : r ≅ t) (s)
  proof: rfl

中文:
定理 ofIsoLimit_lift
  条件: {r t : 锥 F} (P : 是极限 r) (i : r ≅ t) (s)
  证明: rfl
-/
theorem ofIsoLimit_lift {r t : Cone F} (P : IsLimit r) (i : r ≅ t) (s) :
    (P.ofIsoLimit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
@[to_dual /-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/]
/--
Definition of `equivIsoLimit` / `equivIsoLimit` 的定义

English:
definition equivIsoLimit
  signature: {r t : Cone F} (i : r ≅ t)
  body: h.ofIsoLimit i
  invFun h := h.ofIsoLimit i.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]

中文:
定义 equivIsoLimit
  签名: {r t : 锥 F} (i : r ≅ t)
  定义体: h.ofIsoLimit i
  invFun h := h.ofIsoLimit i.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]

Depends on / 依赖: h.ofIsoLimit, ofIsoLimit
-/
def equivIsoLimit {r t : Cone F} (i : r ≅ t) : IsLimit r ≃ IsLimit t where
  toFun h := h.ofIsoLimit i
  invFun h := h.ofIsoLimit i.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]
/--
theorem `equivIsoLimit_apply` / 定理 `equivIsoLimit_apply`

English:
theorem equivIsoLimit_apply
  given: {r t : Cone F} (i : r ≅ t) (P : IsLimit r)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 equivIsoLimit_apply
  条件: {r t : 锥 F} (i : r ≅ t) (P : 是极限 r)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem equivIsoLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit r) :
    equivIsoLimit i P = P.ofIsoLimit i :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `equivIsoLimit_symm_apply` / 定理 `equivIsoLimit_symm_apply`

English:
theorem equivIsoLimit_symm_apply
  given: {r t : Cone F} (i : r ≅ t) (P : IsLimit t)
  proof: rfl

中文:
定理 equivIsoLimit_symm_apply
  条件: {r t : 锥 F} (i : r ≅ t) (P : 是极限 t)
  证明: rfl
-/
theorem equivIsoLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit t) :
    (equivIsoLimit i).symm P = P.ofIsoLimit i.symm :=
  rfl

/-- If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
@[to_dual
/-- If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/]
/--
Definition of `ofPointIso` / `ofPointIso` 的定义

English:
definition ofPointIso
  signature: {r t : Cone F} (P : IsLimit r) [i : IsIso (P.lift t)]
  body: ofIsoLimit P (by
    haveI : IsIso (P.liftConeMorphism t).hom := i
    haveI : IsIso (P.liftConeMorphism t) := Cone.cone_iso_of_hom_iso _
    symm
    apply asIso (P.liftConeMorphism t))

中文:
定义 ofPointIso
  签名: {r t : 锥 F} (P : 是极限 r) [i : 是同构 (P.lift t)]
  定义体: ofIsoLimit P (by
    haveI : IsIso (P.liftConeMorphism t).hom := i
    haveI : IsIso (P.liftConeMorphism t) := Cone.cone_iso_of_hom_iso _
    symm
    apply asIso (P.liftConeMorphism t))

Depends on / 依赖: Cone.cone_iso_of_hom_iso, P.liftConeMorphism, cone_iso_of_hom_iso, liftConeMorphism, ofIsoLimit
-/
def ofPointIso {r t : Cone F} (P : IsLimit r) [i : IsIso (P.lift t)] : IsLimit t :=
  ofIsoLimit P (by
    haveI : IsIso (P.liftConeMorphism t).hom := i
    haveI : IsIso (P.liftConeMorphism t) := Cone.cone_iso_of_hom_iso _
    symm
    apply asIso (P.liftConeMorphism t))

variable {t : Cone F}

@[to_dual]
/--
theorem `hom_lift` / 定理 `hom_lift`

English:
theorem hom_lift
  given: (h : IsLimit t) {W : C} (m : W ⟶ t.pt)
  proof: h.uniq { pt := W, π := { app := fun b => m ≫ t.π.app b } } m fun _ => rfl

中文:
定理 hom_lift
  条件: (h : 是极限 t) {W : C} (m : W ⟶ t.pt)
  证明: h.uniq { pt := W, π := { app := fun b => m ≫ t.π.app b } } m fun _ => rfl
-/
theorem hom_lift (h : IsLimit t) {W : C} (m : W ⟶ t.pt) :
    m = h.lift { pt := W, π := { app := fun b => m ≫ t.π.app b } } :=
  h.uniq { pt := W, π := { app := fun b => m ≫ t.π.app b } } m fun _ => rfl

/-- Two morphisms into a limit are equal if their compositions with
each cone morphism are equal. -/
@[to_dual /-- Two morphisms out of a colimit are equal if their compositions with
each cocone morphism are equal. -/]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (h : IsLimit t) {W : C} {f f' : W ⟶ t.pt}
  proof: by
  rw [h.hom_lift f]; rw [h.hom_lift f']; congr; exact funext w

@[to_dual]

中文:
定理 hom_ext
  结论: (h : 是极限 t) {W : C} {f f' : W ⟶ t.pt}
  证明: by
  rw [h.hom_lift f]; rw [h.hom_lift f']; congr; exact funext w

@[to_dual]

Depends on / 依赖: h.hom_lift, hom_lift
-/
theorem hom_ext (h : IsLimit t) {W : C} {f f' : W ⟶ t.pt}
    (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) :
    f = f' := by
  rw [h.hom_lift f]; rw [h.hom_lift f']; congr; exact funext w

@[to_dual]
/--
lemma `nonempty_isLimit_iff_isIso_lift` / 引理 `nonempty_isLimit_iff_isIso_lift`

English:
lemma nonempty_isLimit_iff_isIso_lift
  given: {s t : Cone F} (hs : IsLimit s)
  proof: ⟨fun ⟨ht⟩ => ⟨ht.lift s, ht.hom_ext (by simp), hs.hom_ext (by simp)⟩, fun h => ⟨hs.ofPointIso⟩⟩

中文:
引理 nonempty_isLimit_iff_isIso_lift
  条件: {s t : 锥 F} (hs : 是极限 s)
  证明: ⟨fun ⟨ht⟩ => ⟨ht.lift s, ht.hom_ext (by simp), hs.hom_ext (by simp)⟩, fun h => ⟨hs.ofPointIso⟩⟩

Depends on / 依赖: hom_ext, hs.hom_ext, hs.ofPointIso, ht.hom_ext, ht.lift, ofPointIso
-/
lemma nonempty_isLimit_iff_isIso_lift {s t : Cone F} (hs : IsLimit s) :
    Nonempty (IsLimit t) ↔ IsIso (hs.lift t) :=
  ⟨fun ⟨ht⟩ => ⟨ht.lift s, ht.hom_ext (by simp), hs.hom_ext (by simp)⟩, fun h => ⟨hs.ofPointIso⟩⟩

/-- Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
@[to_dual
/-- Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/]
/--
Definition of `ofRightAdjoint` / `ofRightAdjoint` 的定义

English:
definition ofRightAdjoint
  signature: {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} {left : Cone F ⥤ Cone G}
  body: mkConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))
    fun _ _ => (Adjunction.eq_homEquiv_apply _ _ _).2 t.uniq_cone_morphism

中文:
定义 ofRightAdjoint
  签名: {D : 类型u₄} [范畴.{v₄} D] {G : K ⥤ D} {left : 锥 F ⥤ 锥 G}
  定义体: mkConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))
    fun _ _ => (Adjunction.eq_homEquiv_apply _ _ _).2 t.uniq_cone_morphism

Depends on / 依赖: Adjunction, Adjunction.eq_homEquiv_apply, adj.homEquiv, eq_homEquiv_apply, homEquiv, liftConeMorphism, mkConeMorphism, t.liftConeMorphism, t.uniq_cone_morphism, uniq_cone_morphism
-/
def ofRightAdjoint {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} {left : Cone F ⥤ Cone G}
    {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsLimit c) : IsLimit (right.obj c) :=
  mkConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))
    fun _ _ => (Adjunction.eq_homEquiv_apply _ _ _).2 t.uniq_cone_morphism

/--
Definition of `ofConeEquiv` / `ofConeEquiv` 的定义

English:
definition ofConeEquiv
  signature: {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G}
  body: ofIsoLimit (ofRightAdjoint h.toAdjunction P) (h.unitIso.symm.app c)
  invFun := ofRightAdjoint h.symm.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 ofConeEquiv
  签名: {D : 类型u₄} [范畴.{v₄} D] {G : K ⥤ D} (h : 锥 G ≌ 锥 F) {c : 锥 G}
  定义体: ofIsoLimit (ofRightAdjoint h.toAdjunction P) (h.unitIso.symm.app c)
  invFun := ofRightAdjoint h.symm.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: h.toAdjunction, h.unitIso.symm.app, ofIsoLimit, ofRightAdjoint, toAdjunction, unitIso
-/
def ofConeEquiv {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    IsLimit (h.functor.obj c) ≃ IsLimit c where
  toFun P := ofIsoLimit (ofRightAdjoint h.toAdjunction P) (h.unitIso.symm.app c)
  invFun := ofRightAdjoint h.symm.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
@[to_dual existing]
/--
Definition of `_root_.CategoryTheory.Limits.IsColimit.ofCoconeEquiv` / `_root_.CategoryTheory.Limits.IsColimit.ofCoconeEquiv` 的定义

English:
definition _root_.CategoryTheory.Limits.IsColimit.ofCoconeEquiv
  signature: {D : Type u₄} [Category.{v₄} D]
  body: IsColimit.ofIsoColimit (IsColimit.ofLeftAdjoint h.symm.toAdjunction P)
    (h.unitIso.symm.app c)
  invFun := IsColimit.ofLeftAdjoint h.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]

中文:
定义 _root_.范畴论.Limits.是余极限.ofCoconeEquiv
  签名: {D : 类型u₄} [范畴.{v₄} D]
  定义体: IsColimit.ofIsoColimit (IsColimit.ofLeftAdjoint h.symm.toAdjunction P)
    (h.unitIso.symm.app c)
  invFun := IsColimit.ofLeftAdjoint h.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, IsColimit.ofLeftAdjoint, h.symm.toAdjunction, ofIsoColimit, ofLeftAdjoint, toAdjunction
-/
def _root_.CategoryTheory.Limits.IsColimit.ofCoconeEquiv {D : Type u₄} [Category.{v₄} D]
    {G : K ⥤ D} (h : Cocone G ≌ Cocone F) {c : Cocone G} :
    IsColimit (h.functor.obj c) ≃ IsColimit c where
  toFun P := IsColimit.ofIsoColimit (IsColimit.ofLeftAdjoint h.symm.toAdjunction P)
    (h.unitIso.symm.app c)
  invFun := IsColimit.ofLeftAdjoint h.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]
/--
theorem `ofConeEquiv_apply_lift` / 定理 `ofConeEquiv_apply_lift`

English:
theorem ofConeEquiv_apply_lift
  statement: {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 ofConeEquiv_apply_lift
  结论: {D : 类型u₄} [范畴.{v₄} D] {G : K ⥤ D} (h : 锥 G ≌ 锥 F)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem ofConeEquiv_apply_lift {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F)
    {c : Cone G} (P : IsLimit (h.functor.obj c)) (s) :
    (ofConeEquiv h P).lift s =
      ((h.unitIso.hom.app s).hom ≫ (h.inverse.map (P.liftConeMorphism (h.functor.obj s))).hom) ≫
        (h.unitIso.inv.app c).hom :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofConeEquiv_symm_apply_lift` / 定理 `ofConeEquiv_symm_apply_lift`

English:
theorem ofConeEquiv_symm_apply_lift
  statement: {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D}
  proof: rfl

@[deprecated (since := "2026-06-21")] alias ofConeEquiv_apply_desc := ofConeEquiv_apply_lift
@[deprecated (since := "2026-06-21")]
alias ofConeEquiv_symm_apply_desc := ofConeEquiv_symm_apply_lift

中文:
定理 ofConeEquiv_symm_apply_lift
  结论: {D : 类型u₄} [范畴.{v₄} D] {G : K ⥤ D}
  证明: rfl

@[deprecated (since := "2026-06-21")] alias ofConeEquiv_apply_desc := ofConeEquiv_apply_lift
@[deprecated (since := "2026-06-21")]
alias ofConeEquiv_symm_apply_desc := ofConeEquiv_symm_apply_lift
-/
theorem ofConeEquiv_symm_apply_lift {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D}
    (h : Cone G ≌ Cone F) {c : Cone G} (P : IsLimit c) (s) :
    ((ofConeEquiv h).symm P).lift s =
      (h.counitIso.inv.app s).hom ≫ (h.functor.map (P.liftConeMorphism (h.inverse.obj s))).hom :=
  rfl

@[deprecated (since := "2026-06-21")] alias ofConeEquiv_apply_desc := ofConeEquiv_apply_lift
@[deprecated (since := "2026-06-21")]
alias ofConeEquiv_symm_apply_desc := ofConeEquiv_symm_apply_lift

/-- A cone postcomposed with a natural isomorphism is a limit cone
if and only if the original cone is.
-/
@[to_dual precomposeInvEquiv
/-- A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/]
/--
Definition of `postcomposeHomEquiv` / `postcomposeHomEquiv` 的定义

English:
definition postcomposeHomEquiv
  signature: {F G : J ⥤ C} (α : F ≅ G) (c : Cone F)
  body: ofConeEquiv (Cone.postcomposeEquivalence α)

中文:
定义 postcomposeHomEquiv
  签名: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 F)
  定义体: ofConeEquiv (Cone.postcomposeEquivalence α)

Depends on / 依赖: Cone.postcomposeEquivalence, ofConeEquiv, postcomposeEquivalence
-/
def postcomposeHomEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    IsLimit ((Cone.postcompose α.hom).obj c) ≃ IsLimit c :=
  ofConeEquiv (Cone.postcomposeEquivalence α)

/-- A cone postcomposed with the inverse of a natural isomorphism is a limit cone
if and only if the original cone is.
-/
@[to_dual precomposeHomEquiv
/-- A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/]
/--
Definition of `postcomposeInvEquiv` / `postcomposeInvEquiv` 的定义

English:
definition postcomposeInvEquiv
  signature: {F G : J ⥤ C} (α : F ≅ G) (c : Cone G)
  body: postcomposeHomEquiv α.symm c

中文:
定义 postcomposeInvEquiv
  签名: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 G)
  定义体: postcomposeHomEquiv α.symm c

Depends on / 依赖: postcomposeHomEquiv
-/
def postcomposeInvEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    IsLimit ((Cone.postcompose α.inv).obj c) ≃ IsLimit c :=
  postcomposeHomEquiv α.symm c

/-- Constructing an equivalence `IsLimit c ≃ IsLimit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/
@[to_dual
/-- Constructing an equivalence `isColimit c ≃ isColimit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/]
/--
Definition of `equivOfNatIsoOfIso` / `equivOfNatIsoOfIso` 的定义

English:
definition equivOfNatIsoOfIso
  signature: {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
  body: (postcomposeHomEquiv α _).symm.trans (equivIsoLimit w)

中文:
定义 equivOf自然数IsoOfIso
  签名: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 F) (d : 锥 G)
  定义体: (postcomposeHomEquiv α _).symm.trans (equivIsoLimit w)

Depends on / 依赖: equivIsoLimit, postcomposeHomEquiv, symm.trans
-/
def equivOfNatIsoOfIso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
    (w : (Cone.postcompose α.hom).obj c ≅ d) : IsLimit c ≃ IsLimit d :=
  (postcomposeHomEquiv α _).symm.trans (equivIsoLimit w)

set_option linter.translate.warnInvalid false in
/-- The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[to_dual (attr := simps)
/-- The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/]
/--
Definition of `conePointsIsoOfNatIso` / `conePointsIsoOfNatIso` 的定义

English:
definition conePointsIsoOfNatIso
  signature: {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
  body: Q.map s w.hom
  inv := P.map t w.inv
  hom_inv_id := P.hom_ext (by simp)
  inv_hom_id := Q.hom_ext (by simp)

中文:
定义 conePointsIsoOf自然数Iso
  签名: {F G : J ⥤ C} {s : 锥 F} {t : 锥 G} (P : 是极限 s) (Q : 是极限 t)
  定义体: Q.map s w.hom
  inv := P.map t w.inv
  hom_inv_id := P.hom_ext (by simp)
  inv_hom_id := Q.hom_ext (by simp)

Depends on / 依赖: Q.map, w.hom
-/
def conePointsIsoOfNatIso {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
    (w : F ≅ G) : s.pt ≅ t.pt where
  hom := Q.map s w.hom
  inv := P.map t w.inv
  hom_inv_id := P.hom_ext (by simp)
  inv_hom_id := Q.hom_ext (by simp)

attribute [to_dual existing coconePointsIsoOfNatIso_inv] conePointsIsoOfNatIso_hom
attribute [to_dual existing coconePointsIsoOfNatIso_hom] conePointsIsoOfNatIso_inv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
@[to_dual (attr := reassoc) comp_coconePointsIsoOfNatIso_inv]
/--
theorem `conePointsIsoOfNatIso_hom_comp` / 定理 `conePointsIsoOfNatIso_hom_comp`

English:
theorem conePointsIsoOfNatIso_hom_comp
  statement: {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
  proof: by simp

#adaptation_note

中文:
定理 conePointsIsoOf自然数Iso_hom_comp
  结论: {F G : J ⥤ C} {s : 锥 F} {t : 锥 G} (P : 是极限 s)
  证明: by simp

#adaptation_note
-/
theorem conePointsIsoOfNatIso_hom_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (w : F ≅ G) (j : J) :
    (conePointsIsoOfNatIso P Q w).hom ≫ t.π.app j = s.π.app j ≫ w.hom.app j := by simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
@[to_dual (attr := reassoc) comp_coconePointsIsoOfNatIso_hom]
/--
theorem `conePointsIsoOfNatIso_inv_comp` / 定理 `conePointsIsoOfNatIso_inv_comp`

English:
theorem conePointsIsoOfNatIso_inv_comp
  statement: {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
  proof: by simp

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_inv_desc]

中文:
定理 conePointsIsoOf自然数Iso_inv_comp
  结论: {F G : J ⥤ C} {s : 锥 F} {t : 锥 G} (P : 是极限 s)
  证明: by simp

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_inv_desc]
-/
theorem conePointsIsoOfNatIso_inv_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (w : F ≅ G) (j : J) :
    (conePointsIsoOfNatIso P Q w).inv ≫ s.π.app j = t.π.app j ≫ w.inv.app j := by simp

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_inv_desc]
/--
theorem `lift_comp_conePointsIsoOfNatIso_hom` / 定理 `lift_comp_conePointsIsoOfNatIso_hom`

English:
theorem lift_comp_conePointsIsoOfNatIso_hom
  statement: {F G : J ⥤ C} {r s : Cone F} {t : Cone G}
  proof: Q.hom_ext (by simp)

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_hom_desc]

中文:
定理 lift_comp_conePointsIsoOf自然数Iso_hom
  结论: {F G : J ⥤ C} {r s : 锥 F} {t : 锥 G}
  证明: Q.hom_ext (by simp)

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_hom_desc]

Depends on / 依赖: Q.hom_ext, hom_ext
-/
theorem lift_comp_conePointsIsoOfNatIso_hom {F G : J ⥤ C} {r s : Cone F} {t : Cone G}
    (P : IsLimit s) (Q : IsLimit t) (w : F ≅ G) :
    P.lift r ≫ (conePointsIsoOfNatIso P Q w).hom = Q.map r w.hom :=
  Q.hom_ext (by simp)

@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_hom_desc]
/--
theorem `lift_comp_conePointsIsoOfNatIso_inv` / 定理 `lift_comp_conePointsIsoOfNatIso_inv`

English:
theorem lift_comp_conePointsIsoOfNatIso_inv
  statement: {F G : J ⥤ C} {r s : Cone G} {t : Cone F}
  proof: P.hom_ext (by simp)

中文:
定理 lift_comp_conePointsIsoOf自然数Iso_inv
  结论: {F G : J ⥤ C} {r s : 锥 G} {t : 锥 F}
  证明: P.hom_ext (by simp)

Depends on / 依赖: P.hom_ext, hom_ext
-/
theorem lift_comp_conePointsIsoOfNatIso_inv {F G : J ⥤ C} {r s : Cone G} {t : Cone F}
    (P : IsLimit t) (Q : IsLimit s) (w : F ≅ G) :
    Q.lift r ≫ (conePointsIsoOfNatIso P Q w).inv = P.map r w.inv :=
  P.hom_ext (by simp)

section Equivalence

open CategoryTheory.Equivalence

/--
Definition of `whiskerEquivalence` / `whiskerEquivalence` 的定义

English:
definition whiskerEquivalence
  signature: {s : Cone F} (P : IsLimit s) (e : K ≌ J)
  body: ofRightAdjoint (Cone.whiskeringEquivalence e).symm.toAdjunction P

中文:
定义 whiskerEquivalence
  签名: {s : 锥 F} (P : 是极限 s) (e : K ≌ J)
  定义体: ofRightAdjoint (Cone.whiskeringEquivalence e).symm.toAdjunction P

Depends on / 依赖: Cone.whiskeringEquivalence, ofRightAdjoint, symm.toAdjunction, toAdjunction, whiskeringEquivalence
-/
def whiskerEquivalence {s : Cone F} (P : IsLimit s) (e : K ≌ J) : IsLimit (s.whisker e.functor) :=
  ofRightAdjoint (Cone.whiskeringEquivalence e).symm.toAdjunction P

/-- If `s : Cocone F` is a colimit cocone, so is `s` whiskered by an equivalence `e`. -/
@[to_dual existing]
/--
Definition of `_root_.CategoryTheory.Limits.IsColimit.whiskerEquivalence` / `_root_.CategoryTheory.Limits.IsColimit.whiskerEquivalence` 的定义

English:
definition _root_.CategoryTheory.Limits.IsColimit.whiskerEquivalence
  signature: {s : Cocone F}
  body: IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).toAdjunction P

中文:
定义 _root_.范畴论.Limits.是余极限.whiskerEquivalence
  签名: {s : 余锥 F}
  定义体: IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).toAdjunction P

Depends on / 依赖: Cocone, Cocone.whiskeringEquivalence, IsColimit, IsColimit.ofLeftAdjoint, ofLeftAdjoint, toAdjunction, whiskeringEquivalence
-/
def _root_.CategoryTheory.Limits.IsColimit.whiskerEquivalence {s : Cocone F}
    (P : IsColimit s) (e : K ≌ J) : IsColimit (s.whisker e.functor) :=
  IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).toAdjunction P

/--
Definition of `ofWhiskerEquivalence` / `ofWhiskerEquivalence` 的定义

English:
definition ofWhiskerEquivalence
  signature: {s : Cone F} (e : K ≌ J) (P : IsLimit (s.whisker e.functor))
  body: equivIsoLimit ((Cone.whiskeringEquivalence e).unitIso.app s).symm
    (ofRightAdjoint (Cone.whiskeringEquivalence e).toAdjunction P)

中文:
定义 ofWhiskerEquivalence
  签名: {s : 锥 F} (e : K ≌ J) (P : 是极限 (s.whisker e.functor))
  定义体: equivIsoLimit ((Cone.whiskeringEquivalence e).unitIso.app s).symm
    (ofRightAdjoint (Cone.whiskeringEquivalence e).toAdjunction P)

Depends on / 依赖: Cone.whiskeringEquivalence, equivIsoLimit, ofRightAdjoint, toAdjunction, unitIso, unitIso.app, whiskeringEquivalence
-/
def ofWhiskerEquivalence {s : Cone F} (e : K ≌ J) (P : IsLimit (s.whisker e.functor)) : IsLimit s :=
  equivIsoLimit ((Cone.whiskeringEquivalence e).unitIso.app s).symm
    (ofRightAdjoint (Cone.whiskeringEquivalence e).toAdjunction P)

/-- If `s : Cocone F` whiskered by an equivalence `e` is a colimit cocone, so is `s`. -/
@[to_dual existing]
/--
Definition of `_root_.CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence` / `_root_.CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence` 的定义

English:
definition _root_.CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence
  signature: {s : Cocone F} (e : K ≌ J)
  body: IsColimit.equivIsoColimit ((Cocone.whiskeringEquivalence e).unitIso.app s).symm
    (IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).symm.toAdjunction P)

中文:
定义 _root_.范畴论.Limits.是余极限.ofWhiskerEquivalence
  签名: {s : 余锥 F} (e : K ≌ J)
  定义体: IsColimit.equivIsoColimit ((Cocone.whiskeringEquivalence e).unitIso.app s).symm
    (IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).symm.toAdjunction P)

Depends on / 依赖: Cocone, Cocone.whiskeringEquivalence, IsColimit, IsColimit.equivIsoColimit, IsColimit.ofLeftAdjoint, equivIsoColimit, ofLeftAdjoint, symm.toAdjunction, toAdjunction, unitIso, unitIso.app, whiskeringEquivalence
-/
def _root_.CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence {s : Cocone F} (e : K ≌ J)
    (P : IsColimit (s.whisker e.functor)) : IsColimit s :=
  IsColimit.equivIsoColimit ((Cocone.whiskeringEquivalence e).unitIso.app s).symm
    (IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).symm.toAdjunction P)

/-- Given an equivalence of diagrams `e`, `s` is a limit cone iff `s.whisker e.functor` is. -/
@[to_dual
/-- Given an equivalence of diagrams `e`, `s` is a colimit cocone iff `s.whisker e.functor` is. -/]
/--
Definition of `whiskerEquivalenceEquiv` / `whiskerEquivalenceEquiv` 的定义

English:
definition whiskerEquivalenceEquiv
  signature: {s : Cone F} (e : K ≌ J)
  body: ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by cat_disch, by cat_disch⟩

中文:
定义 whiskerEquivalenceEquiv
  签名: {s : 锥 F} (e : K ≌ J)
  定义体: ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by cat_disch, by cat_disch⟩

Depends on / 依赖: cat_disch, h.whiskerEquivalence, ofWhiskerEquivalence, whiskerEquivalence
-/
def whiskerEquivalenceEquiv {s : Cone F} (e : K ≌ J) : IsLimit s ≃ IsLimit (s.whisker e.functor) :=
  ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by cat_disch, by cat_disch⟩

/-- A limit cone extended by an isomorphism is a limit cone. -/
@[to_dual /-- A colimit cocone extended by an isomorphism is a colimit cocone. -/]
/--
Definition of `extendIso` / `extendIso` 的定义

English:
definition extendIso
  signature: {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit s)
  body: IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i))

中文:
定义 extendIso
  签名: {s : 锥 F} {X : C} (i : X ⟶ s.pt) [是同构 i] (hs : 是极限 s)
  定义体: IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i))

Depends on / 依赖: Cone.extendIso, IsLimit, IsLimit.ofIsoLimit, extendIso, ofIsoLimit
-/
def extendIso {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit s) :
    IsLimit (s.extend i) :=
  IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i))

/-- A cone is a limit cone if its extension by an isomorphism is. -/
@[to_dual /-- A cocone is a colimit cocone if its extension by an isomorphism is. -/]
/--
Definition of `ofExtendIso` / `ofExtendIso` 的定义

English:
definition ofExtendIso
  signature: {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit (s.extend i))
  body: IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i)).symm

中文:
定义 ofExtendIso
  签名: {s : 锥 F} {X : C} (i : X ⟶ s.pt) [是同构 i] (hs : 是极限 (s.extend i))
  定义体: IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i)).symm

Depends on / 依赖: Cone.extendIso, IsLimit, IsLimit.ofIsoLimit, extendIso, ofIsoLimit
-/
def ofExtendIso {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit (s.extend i)) :
    IsLimit s :=
  IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i)).symm

/-- A cone is a limit cone iff its extension by an isomorphism is. -/
@[to_dual /-- A cocone is a colimit cocone iff its extension by an isomorphism is. -/]
/--
Definition of `extendIsoEquiv` / `extendIsoEquiv` 的定义

English:
definition extendIsoEquiv
  signature: {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i]
  body: equivOfSubsingletonOfSubsingleton (extendIso i) (ofExtendIso i)

中文:
定义 extendIsoEquiv
  签名: {s : 锥 F} {X : C} (i : X ⟶ s.pt) [是同构 i]
  定义体: equivOfSubsingletonOfSubsingleton (extendIso i) (ofExtendIso i)

Depends on / 依赖: equivOfSubsingletonOfSubsingleton, extendIso, ofExtendIso
-/
def extendIsoEquiv {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] :
    IsLimit s ≃ IsLimit (s.extend i) :=
  equivOfSubsingletonOfSubsingleton (extendIso i) (ofExtendIso i)

set_option backward.defeqAttrib.useBackward true in
set_option linter.translate.warnInvalid false in
/-- We can prove two cone points `(s : Cone F).pt` and `(t : Cone G).pt` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[to_dual (attr := simps)
/-- We can prove two cocone points `(s : Cocone F).pt` and `(t : Cocone G).pt` are isomorphic if
* both cocones are colimit cocones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/]
/--
Definition of `conePointsIsoOfEquivalence` / `conePointsIsoOfEquivalence` 的定义

English:
definition conePointsIsoOfEquivalence
  signature: {F : J ⥤ C} {s : Cone F} {G : K ⥤ C} {t : Cone G} (P : IsLimit s)
  body: let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { hom := Q.lift ((Cone.equivalenceOfReindexing e.symm w').functor.obj s)
    inv := P.lift ((Cone.equivalenceOfReindexing e w).functor.obj t)
    hom_inv_id := by
      apply hom_ext P; intro j
      dsimp [w']
  

中文:
定义 conePointsIsoOfEquivalence
  签名: {F : J ⥤ C} {s : 锥 F} {G : K ⥤ C} {t : 锥 G} (P : 是极限 s)
  定义体: let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { hom := Q.lift ((Cone.equivalenceOfReindexing e.symm w').functor.obj s)
    inv := P.lift ((Cone.equivalenceOfReindexing e w).functor.obj t)
    hom_inv_id := by
      apply hom_ext P; intro j
      dsimp [w']
  

Depends on / 依赖: Cone.equivalenceOfReindexing, Functor, Functor.comp_map, L.map, L.map_comp, LeftFraction, LeftFraction.map_comp_map_s_assoc, Limits, Limits.Cone.postcompose_obj_, Limits.Cone.whisker_, MorphismProperty, MorphismProperty.LeftFraction.map_eq_iff, NatTrans, NatTrans.comp_app, P.lift, Q.lift, W.LeftFraction, cancel_mono, choose_spec, comp_app
-/
def conePointsIsoOfEquivalence {F : J ⥤ C} {s : Cone F} {G : K ⥤ C} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.pt ≅ t.pt :=
  let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { hom := Q.lift ((Cone.equivalenceOfReindexing e.symm w').functor.obj s)
    inv := P.lift ((Cone.equivalenceOfReindexing e w).functor.obj t)
    hom_inv_id := by
      apply hom_ext P; intro j
      dsimp [w']
      simp only [Limits.Cone.whisker_π, Limits.Cone.postcompose_obj_π, fac, whiskerLeft_app,
        assoc, id_comp, invFunIdAssoc_hom_app, fac_assoc, NatTrans.comp_app]
      rw [counit_app_functor]; rw [← Functor.comp_map]; rw [← w.inv.naturality_assoc]
      simp
    inv_hom_id := by
      apply hom_ext Q
      cat_disch }

attribute [to_dual existing coconePointsIsoOfEquivalence_inv] conePointsIsoOfEquivalence_hom
attribute [to_dual existing coconePointsIsoOfEquivalence_hom] conePointsIsoOfEquivalence_inv

end Equivalence

/-- The universal property of a limit cone: a map `W ⟶ t.pt` is the same as
a cone on `F` with cone point `W`. -/
@[to_dual (attr := simps apply)
/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
a cocone on `F` with cone point `W`. -/]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: (h : IsLimit t) {W : C}
  body: (t.extend f).π
  invFun π := h.lift (Cone.mk _ π)
  left_inv f := h.hom_ext (by simp)
  right_inv π := by cat_disch

@[to_dual (attr := reassoc (attr := simp)) ι_app_homEquiv_symm]

中文:
定义 homEquiv
  签名: (h : 是极限 t) {W : C}
  定义体: (t.extend f).π
  invFun π := h.lift (Cone.mk _ π)
  left_inv f := h.hom_ext (by simp)
  right_inv π := by cat_disch

@[to_dual (attr := reassoc (attr := simp)) ι_app_homEquiv_symm]

Depends on / 依赖: extend, t.extend
-/
def homEquiv (h : IsLimit t) {W : C} : (W ⟶ t.pt) ≃ ((Functor.const J).obj W ⟶ F) where
  toFun f := (t.extend f).π
  invFun π := h.lift (Cone.mk _ π)
  left_inv f := h.hom_ext (by simp)
  right_inv π := by cat_disch

@[to_dual (attr := reassoc (attr := simp)) ι_app_homEquiv_symm]
/--
lemma `homEquiv_symm_π_app` / 引理 `homEquiv_symm_π_app`

English:
lemma homEquiv_symm_π_app
  statement: (h : IsLimit t) {W : C}
  proof: by
  simp [homEquiv]

@[to_dual]

中文:
引理 homEquiv_symm_π_app
  结论: (h : 是极限 t) {W : C}
  证明: by
  simp [homEquiv]

@[to_dual]

Depends on / 依赖: L.map, W.LeftFraction, add.map, cancel_mono, choose_spec, fst.map, homEquiv, inverts, map_eq_iff, nth_, snd.map
-/
lemma homEquiv_symm_π_app (h : IsLimit t) {W : C}
    (f : (const J).obj W ⟶ F) (j : J) :
    h.homEquiv.symm f ≫ t.π.app j = f.app j := by
  simp [homEquiv]

@[to_dual]
/--
lemma `homEquiv_symm_naturality` / 引理 `homEquiv_symm_naturality`

English:
lemma homEquiv_symm_naturality
  statement: (h : IsLimit t) {W W' : C}
  proof: h.homEquiv.injective (by aesop)

中文:
引理 homEquiv_symm_naturality
  结论: (h : 是极限 t) {W W' : C}
  证明: h.homEquiv.injective (by aesop)

Depends on / 依赖: h.homEquiv.injective, homEquiv, injective, symm_add
-/
lemma homEquiv_symm_naturality (h : IsLimit t) {W W' : C}
    (f : (const J).obj W ⟶ F) (g : W' ⟶ W) :
    h.homEquiv.symm ((Functor.const _).map g ≫ f) = g ≫ h.homEquiv.symm f :=
  h.homEquiv.injective (by aesop)

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
a cone on `F` with cone point `W`. -/
@[to_dual
/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
a cocone on `F` with cone point `W`. -/]
/--
Definition of `homIso` / `homIso` 的定义

English:
definition homIso
  signature: (h : IsLimit t) (W : C)
  body: Equiv.toIso (Equiv.ulift.trans h.homEquiv)

中文:
定义 homIso
  签名: (h : 是极限 t) (W : C)
  定义体: Equiv.toIso (Equiv.ulift.trans h.homEquiv)

Depends on / 依赖: Equiv.toIso, Equiv.ulift.trans, L.map, L.map_comp, LeftFraction, LeftFraction.map_comp_map_s, Limits, Limits.zero_comp, add_zero, cancel_mono, exists_leftFraction, h.homEquiv, homEquiv, map_comp, map_comp_map_s, zero_comp
-/
def homIso (h : IsLimit t) (W : C) : ULift.{u₁} (W ⟶ t.pt : Type v₃) ≅ (const J).obj W ⟶ F :=
  Equiv.toIso (Equiv.ulift.trans h.homEquiv)

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
@[simp]
/--
theorem `homIso_hom` / 定理 `homIso_hom`

English:
theorem homIso_hom
  given: (h : IsLimit t) {W : C}
  proof: rfl

中文:
定理 homIso_hom
  条件: (h : 是极限 t) {W : C}
  证明: rfl
-/
theorem homIso_hom (h : IsLimit t) {W : C} :
    (IsLimit.homIso h W).hom = ↾fun f => (t.extend f.down).π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `natIso` / `natIso` 的定义

English:
definition natIso
  signature: (h : IsLimit t)
  body: by
  refine NatIso.ofComponents (fun W => IsLimit.homIso h (unop W))

中文:
定义 natIso
  签名: (h : 是极限 t)
  定义体: by
  refine NatIso.ofComponents (fun W => IsLimit.homIso h (unop W))

Depends on / 依赖: IsLimit, IsLimit.homIso, L.map, L.map_comp, LeftFraction, LeftFraction.map_comp_map_s, Limits, Limits.zero_comp, NatIso, NatIso.ofComponents, cancel_mono, exists_leftFraction, homIso, map_comp, map_comp_map_s, neg_add_cancel, ofComponents, zero_comp
-/
def natIso (h : IsLimit t) : yoneda.obj t.pt ⋙ uliftFunctor.{u₁} ≅ F.cones := by
  refine NatIso.ofComponents (fun W => IsLimit.homIso h (unop W))

/--
Definition of `homIso'` / `homIso'` 的定义

English:
definition homIso'
  signature: (h : IsLimit t) (W : C)
  body: h.homIso W ≪≫
    { hom := ↾fun π =>
        ⟨fun j => π.app j, fun f => by convert! ← (π.naturality f).symm; apply id_comp⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [id_comp]; exact (p.2 f).symm } }

中文:
定义 homIso'
  签名: (h : 是极限 t) (W : C)
  定义体: h.homIso W ≪≫
    { hom := ↾fun π =>
        ⟨fun j => π.app j, fun f => by convert! ← (π.naturality f).symm; apply id_comp⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [id_comp]; exact (p.2 f).symm } }

Depends on / 依赖: add_assoc, convert, forgetFst, forgetThd, h.homIso, homIso, id_comp, naturality
-/
def homIso' (h : IsLimit t) (W : C) :
    (ULift.{u₁} (W ⟶ t.pt : Type v₃)) ≅
      { p : forall j, W ⟶ F.obj j // forall {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  h.homIso W ≪≫
    { hom := ↾fun π =>
        ⟨fun j => π.app j, fun f => by convert! ← (π.naturality f).symm; apply id_comp⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [id_comp]; exact (p.2 f).symm } }

/-- If `G : C → D` is a faithful functor which sends t to a limit cone,
then it suffices to check that the induced maps for the image of t
can be lifted to maps of `C`. -/
@[to_dual /-- If `G : C → D` is a faithful functor which sends t to a colimit cocone,
then it suffices to check that the induced maps for the image of t
can be lifted to maps of `C`. -/]
/--
Definition of `ofFaithful` / `ofFaithful` 的定义

English:
definition ofFaithful
  signature: {t : Cone F} {D : Type u₄} [Category.{v₄} D] (G : C ⥤ D) [G.Faithful]
  body: { lift
    fac := fun s j => by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac
    uniq := fun s m w => by
      apply G.map_injective; rw [h]
      refine ht.uniq (mapCone G s) _ fun j => ?_
      convert! ← congrArg (fun f => G.map f) (w j)
      apply G.map_comp }

中文:
定义 ofFaithful
  签名: {t : 锥 F} {D : 类型u₄} [范畴.{v₄} D] (G : C ⥤ D) [G.忠实]
  定义体: { lift
    fac := fun s j => by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac
    uniq := fun s m w => by
      apply G.map_injective; rw [h]
      refine ht.uniq (mapCone G s) _ fun j => ?_
      convert! ← congrArg (fun f => G.map f) (w j)
      apply G.map_comp }

Depends on / 依赖: G.map, G.map_comp, G.map_injective, LeftFraction, LeftFraction.map_com, LeftFraction.map_comp_map_eq_map, RightFraction, RightFraction.mk, W.comp_mem, comp_mem, convert, exists_leftFraction, ht.fac, ht.uniq, mapCone, map_com, map_comp, map_comp_map_eq_map, map_injective, rotate_left
-/
def ofFaithful {t : Cone F} {D : Type u₄} [Category.{v₄} D] (G : C ⥤ D) [G.Faithful]
    (ht : IsLimit (mapCone G t)) (lift : forall s : Cone F, s.pt ⟶ t.pt)
    (h : forall s, G.map (lift s) = ht.lift (mapCone G s)) : IsLimit t :=
  { lift
    fac := fun s j => by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac
    uniq := fun s m w => by
      apply G.map_injective; rw [h]
      refine ht.uniq (mapCone G s) _ fun j => ?_
      convert! ← congrArg (fun f => G.map f) (w j)
      apply G.map_comp }

/-- If `F` and `G` are naturally isomorphic, then `F.mapCone c` being a limit implies
`G.mapCone c` is also a limit.
-/
@[to_dual
/-- If `F` and `G` are naturally isomorphic, then `F.mapCocone c` being a colimit implies
`G.mapCocone c` is also a colimit.
-/]
/--
Definition of `mapConeEquiv` / `mapConeEquiv` 的定义

English:
definition mapConeEquiv
  signature: {D : Type u₄} [Category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : Cone K}
  body: by
  apply postcomposeInvEquiv (isoWhiskerLeft K h :) (mapCone G c) _
  apply t.ofIsoLimit (postcomposeWhiskerLeftMapCone h.symm c).symm

中文:
定义 mapConeEquiv
  签名: {D : 类型u₄} [范畴.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : 锥 K}
  定义体: by
  apply postcomposeInvEquiv (isoWhiskerLeft K h :) (mapCone G c) _
  apply t.ofIsoLimit (postcomposeWhiskerLeftMapCone h.symm c).symm

Depends on / 依赖: h.symm, isoWhiskerLeft, mapCone, ofIsoLimit, postcomposeInvEquiv, postcomposeWhiskerLeftMapCone, t.ofIsoLimit
-/
def mapConeEquiv {D : Type u₄} [Category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : Cone K}
    (t : IsLimit (mapCone F c)) : IsLimit (mapCone G c) := by
  apply postcomposeInvEquiv (isoWhiskerLeft K h :) (mapCone G c) _
  apply t.ofIsoLimit (postcomposeWhiskerLeftMapCone h.symm c).symm

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
/--
Definition of `isoUniqueConeMorphism` / `isoUniqueConeMorphism` 的定义

English:
definition isoUniqueConeMorphism
  signature: {t : Cone F}
  body: ↾fun h s =>
    { default := h.liftConeMorphism s
      uniq := fun _ => h.uniq_cone_morphism }
  inv := ↾fun h =>
    { lift := fun s => (h s).default.hom
      uniq := fun s f w => congrArg ConeMorphism.hom ((h s).uniq ⟨f, w⟩) }

中文:
定义 isoUniqueConeMorphism
  签名: {t : 锥 F}
  定义体: ↾fun h s =>
    { default := h.liftConeMorphism s
      uniq := fun _ => h.uniq_cone_morphism }
  inv := ↾fun h =>
    { lift := fun s => (h s).default.hom
      uniq := fun s f w => congrArg ConeMorphism.hom ((h s).uniq ⟨f, w⟩) }

Depends on / 依赖: L.map, LeftFraction, LeftFraction.map_ofHom, W.id_mem, id_mem, map_ofHom
-/
def isoUniqueConeMorphism {t : Cone F} :
    IsLimit t ≅ forall s, Unique (s ⟶ t) where
  hom := ↾fun h s =>
    { default := h.liftConeMorphism s
      uniq := fun _ => h.uniq_cone_morphism }
  inv := ↾fun h =>
    { lift := fun s => (h s).default.hom
      uniq := fun s f w => congrArg ConeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : F.cones.RepresentableBy X)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point
`Y`. -/
@[implicit_reducible]
/--
Definition of `coneOfHom` / `coneOfHom` 的定义

English:
definition coneOfHom
  signature: {Y : C} (f : Y ⟶ X)
  body: Y
  π := h.homEquiv f

中文:
定义 coneOfHom
  签名: {Y : C} (f : Y ⟶ X)
  定义体: Y
  π := h.homEquiv f
-/
def coneOfHom {Y : C} (f : Y ⟶ X) : Cone F where
  pt := Y
  π := h.homEquiv f

/--
Definition of `homOfCone` / `homOfCone` 的定义

English:
definition homOfCone
  signature: (s : Cone F)
  body: h.homEquiv.symm s.π

@[simp]

中文:
定义 homOfCone
  签名: (s : 锥 F)
  定义体: h.homEquiv.symm s.π

@[simp]

Depends on / 依赖: h.homEquiv.symm, homEquiv
-/
def homOfCone (s : Cone F) : s.pt ⟶ X :=
  h.homEquiv.symm s.π

@[simp]
/--
theorem `coneOfHom_homOfCone` / 定理 `coneOfHom_homOfCone`

English:
theorem coneOfHom_homOfCone
  given: (s : Cone F)
  statement: coneOfHom h (homOfCone h s) = s
  proof: by
  dsimp [coneOfHom, homOfCone]
  match s with
  | .mk s_pt s_π =>
    congr
    exact h.homEquiv.apply_symm_apply s_π

@[simp]

中文:
定理 coneOfHom_homOfCone
  条件: (s : 锥 F)
  结论: coneOfHom h (homOfCone h s) = s
  证明: by
  dsimp [coneOfHom, homOfCone]
  match s with
  | .mk s_pt s_π =>
    congr
    exact h.homEquiv.apply_symm_apply s_π

@[simp]

Depends on / 依赖: apply_symm_apply, coneOfHom, h.homEquiv.apply_symm_apply, homEquiv, homOfCone, s_pt
-/
theorem coneOfHom_homOfCone (s : Cone F) : coneOfHom h (homOfCone h s) = s := by
  dsimp [coneOfHom, homOfCone]
  match s with
  | .mk s_pt s_π =>
    congr
    exact h.homEquiv.apply_symm_apply s_π

@[simp]
/--
theorem `homOfCone_coneOfHom` / 定理 `homOfCone_coneOfHom`

English:
theorem homOfCone_coneOfHom
  given: {Y : C} (f : Y ⟶ X)
  statement: homOfCone h (coneOfHom h f) = f
  proof: by
  simp [coneOfHom, homOfCone]

中文:
定理 homOfCone_coneOfHom
  条件: {Y : C} (f : Y ⟶ X)
  结论: homOfCone h (coneOfHom h f) = f
  证明: by
  simp [coneOfHom, homOfCone]

Depends on / 依赖: coneOfHom, homOfCone
-/
theorem homOfCone_coneOfHom {Y : C} (f : Y ⟶ X) : homOfCone h (coneOfHom h f) = f := by
  simp [coneOfHom, homOfCone]

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
@[implicit_reducible]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: coneOfHom h (𝟙 X)

中文:
定义 limitCone
  签名: : 锥 F
  定义体: coneOfHom h (𝟙 X)

Depends on / 依赖: coneOfHom
-/
def limitCone : Cone F :=
  coneOfHom h (𝟙 X)

/--
theorem `coneOfHom_fac` / 定理 `coneOfHom_fac`

English:
theorem coneOfHom_fac
  given: {Y : C} (f : Y ⟶ X)
  statement: coneOfHom h f = (limitCone h).extend f
  proof: by
  dsimp [coneOfHom, limitCone, Cone.extend]
  congr
  conv_lhs => rw [← Category.comp_id f]
  exact h.homEquiv_comp f (𝟙 X)

中文:
定理 coneOfHom_fac
  条件: {Y : C} (f : Y ⟶ X)
  结论: coneOfHom h f = (limitCone h).extend f
  证明: by
  dsimp [coneOfHom, limitCone, Cone.extend]
  congr
  conv_lhs => rw [← Category.comp_id f]
  exact h.homEquiv_comp f (𝟙 X)

Depends on / 依赖: Category, Category.comp_id, Cone.extend, comp_id, coneOfHom, conv_lhs, extend, h.homEquiv_comp, homEquiv_comp, limitCone
-/
theorem coneOfHom_fac {Y : C} (f : Y ⟶ X) : coneOfHom h f = (limitCone h).extend f := by
  dsimp [coneOfHom, limitCone, Cone.extend]
  congr
  conv_lhs => rw [← Category.comp_id f]
  exact h.homEquiv_comp f (𝟙 X)

/--
theorem `cone_fac` / 定理 `cone_fac`

English:
theorem cone_fac
  given: (s : Cone F)
  statement: (limitCone h).extend (homOfCone h s) = s
  proof: by
  rw [← coneOfHom_homOfCone h s]
  conv_lhs => simp only [homOfCone_coneOfHom]
  apply (coneOfHom_fac _ _).symm

中文:
定理 cone_fac
  条件: (s : 锥 F)
  结论: (limitCone h).extend (homOfCone h s) = s
  证明: by
  rw [← coneOfHom_homOfCone h s]
  conv_lhs => simp only [homOfCone_coneOfHom]
  apply (coneOfHom_fac _ _).symm

Depends on / 依赖: coneOfHom_fac, coneOfHom_homOfCone, conv_lhs, homOfCone_coneOfHom
-/
theorem cone_fac (s : Cone F) : (limitCone h).extend (homOfCone h s) = s := by
  rw [← coneOfHom_homOfCone h s]
  conv_lhs => simp only [homOfCone_coneOfHom]
  apply (coneOfHom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/--
Definition of `ofRepresentableBy` / `ofRepresentableBy` 的定义

English:
definition ofRepresentableBy
  signature: {X : C} (h : F.cones.RepresentableBy X)
  body: homOfCone h s
  fac s j := by
    have h := cone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCone_coneOfHom h m]
    congr
    rw [coneOfHom_fac]
    dsimp [Cone.extend]; cases s; congr with j; exact w j

中文:
定义 ofRepresentableBy
  签名: {X : C} (h : F.cones.可表示 X)
  定义体: homOfCone h s
  fac s j := by
    have h := cone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCone_coneOfHom h m]
    congr
    rw [coneOfHom_fac]
    dsimp [Cone.extend]; cases s; congr with j; exact w j

Depends on / 依赖: homOfCone
-/
def ofRepresentableBy {X : C} (h : F.cones.RepresentableBy X) : IsLimit (limitCone h) where
  lift s := homOfCone h s
  fac s j := by
    have h := cone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCone_coneOfHom h m]
    congr
    rw [coneOfHom_fac]
    dsimp [Cone.extend]; cases s; congr with j; exact w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: (hc : IsLimit t)
  body: hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

中文:
定义 representableBy
  签名: (hc : 是极限 t)
  定义体: hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

Depends on / 依赖: hc.homEquiv, homEquiv
-/
def representableBy (hc : IsLimit t) : F.cones.RepresentableBy t.pt where
  homEquiv := hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

end

end IsLimit


namespace IsColimit


variable {t : Cocone F}


@[simp]
/--
theorem `homIso_hom` / 定理 `homIso_hom`

English:
theorem homIso_hom
  given: (h : IsColimit t) {W : C}
  proof: rfl

中文:
定理 homIso_hom
  条件: (h : 是余极限 t) {W : C}
  证明: rfl
-/
theorem homIso_hom (h : IsColimit t) {W : C} :
    (IsColimit.homIso h W).hom = ↾fun f => (t.extend f.down).ι :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `natIso` / `natIso` 的定义

English:
definition natIso
  signature: (h : IsColimit t)
  body: NatIso.ofComponents (IsColimit.homIso h)

中文:
定义 natIso
  签名: (h : 是余极限 t)
  定义体: NatIso.ofComponents (IsColimit.homIso h)

Depends on / 依赖: IsColimit, IsColimit.homIso, NatIso, NatIso.ofComponents, homIso, ofComponents
-/
def natIso (h : IsColimit t) : coyoneda.obj (op t.pt) ⋙ uliftFunctor.{u₁} ≅ F.cocones :=
  NatIso.ofComponents (IsColimit.homIso h)

/--
Definition of `homIso'` / `homIso'` 的定义

English:
definition homIso'
  signature: (h : IsColimit t) (W : C)
  body: h.homIso W ≪≫
    { hom := ↾fun ι =>
        ⟨fun j => ι.app j, fun {j} {j'} f => by convert! ← ι.naturality f; apply comp_id⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [comp_id]; exact p.2 f } }

中文:
定义 homIso'
  签名: (h : 是余极限 t) (W : C)
  定义体: h.homIso W ≪≫
    { hom := ↾fun ι =>
        ⟨fun j => ι.app j, fun {j} {j'} f => by convert! ← ι.naturality f; apply comp_id⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [comp_id]; exact p.2 f } }

Depends on / 依赖: comp_id, convert, h.homIso, homIso, naturality
-/
def homIso' (h : IsColimit t) (W : C) :
    (ULift.{u₁} (t.pt ⟶ W : Type v₃)) ≅
      { p : forall j, F.obj j ⟶ W // forall {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  h.homIso W ≪≫
    { hom := ↾fun ι =>
        ⟨fun j => ι.app j, fun {j} {j'} f => by convert! ← ι.naturality f; apply comp_id⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [comp_id]; exact p.2 f } }


/--
Definition of `isoUniqueCoconeMorphism` / `isoUniqueCoconeMorphism` 的定义

English:
definition isoUniqueCoconeMorphism
  signature: {t : Cocone F}
  body: ↾fun h s =>
    { default := h.descCoconeMorphism s
      uniq := fun _ => h.uniq_cocone_morphism }
  inv := ↾fun h =>
    { desc := fun s => (h s).default.hom
      uniq := fun s f w => congrArg CoconeMorphism.hom ((h s).uniq ⟨f, w⟩) }

中文:
定义 isoUniqueCoconeMorphism
  签名: {t : 余锥 F}
  定义体: ↾fun h s =>
    { default := h.descCoconeMorphism s
      uniq := fun _ => h.uniq_cocone_morphism }
  inv := ↾fun h =>
    { desc := fun s => (h s).default.hom
      uniq := fun s f w => congrArg CoconeMorphism.hom ((h s).uniq ⟨f, w⟩) }
-/
def isoUniqueCoconeMorphism {t : Cocone F} :
    IsColimit t ≅ forall s, Unique (t ⟶ s) where
  hom := ↾fun h s =>
    { default := h.descCoconeMorphism s
      uniq := fun _ => h.uniq_cocone_morphism }
  inv := ↾fun h =>
    { desc := fun s => (h s).default.hom
      uniq := fun s f w => congrArg CoconeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : F.cocones.CorepresentableBy X)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone
point `Y`. -/
@[implicit_reducible]
/--
Definition of `coconeOfHom` / `coconeOfHom` 的定义

English:
definition coconeOfHom
  signature: {Y : C} (f : X ⟶ Y)
  body: Y
  ι := h.homEquiv f

中文:
定义 coconeOfHom
  签名: {Y : C} (f : X ⟶ Y)
  定义体: Y
  ι := h.homEquiv f
-/
def coconeOfHom {Y : C} (f : X ⟶ Y) : Cocone F where
  pt := Y
  ι := h.homEquiv f

/--
Definition of `homOfCocone` / `homOfCocone` 的定义

English:
definition homOfCocone
  signature: (s : Cocone F)
  body: h.homEquiv.symm s.ι

@[simp]

中文:
定义 homOfCocone
  签名: (s : 余锥 F)
  定义体: h.homEquiv.symm s.ι

@[simp]

Depends on / 依赖: h.homEquiv.symm, homEquiv
-/
def homOfCocone (s : Cocone F) : X ⟶ s.pt :=
  h.homEquiv.symm s.ι

@[simp]
/--
theorem `coconeOfHom_homOfCocone` / 定理 `coconeOfHom_homOfCocone`

English:
theorem coconeOfHom_homOfCocone
  given: (s : Cocone F)
  statement: coconeOfHom h (homOfCocone h s) = s
  proof: by
  dsimp [coconeOfHom, homOfCocone]
  match s with
  | .mk s_pt s_ι =>
    congr
    exact h.homEquiv.apply_symm_apply s_ι

@[simp]

中文:
定理 coconeOfHom_homOfCocone
  条件: (s : 余锥 F)
  结论: coconeOfHom h (homOfCocone h s) = s
  证明: by
  dsimp [coconeOfHom, homOfCocone]
  match s with
  | .mk s_pt s_ι =>
    congr
    exact h.homEquiv.apply_symm_apply s_ι

@[simp]

Depends on / 依赖: apply_symm_apply, coconeOfHom, h.homEquiv.apply_symm_apply, homEquiv, homOfCocone, s_pt
-/
theorem coconeOfHom_homOfCocone (s : Cocone F) : coconeOfHom h (homOfCocone h s) = s := by
  dsimp [coconeOfHom, homOfCocone]
  match s with
  | .mk s_pt s_ι =>
    congr
    exact h.homEquiv.apply_symm_apply s_ι

@[simp]
/--
theorem `homOfCocone_coconeOfHom` / 定理 `homOfCocone_coconeOfHom`

English:
theorem homOfCocone_coconeOfHom
  given: {Y : C} (f : X ⟶ Y)
  statement: homOfCocone h (coconeOfHom h f) = f
  proof: by
  simp [homOfCocone, coconeOfHom]

中文:
定理 homOfCocone_coconeOfHom
  条件: {Y : C} (f : X ⟶ Y)
  结论: homOfCocone h (coconeOfHom h f) = f
  证明: by
  simp [homOfCocone, coconeOfHom]

Depends on / 依赖: coconeOfHom, homOfCocone
-/
theorem homOfCocone_coconeOfHom {Y : C} (f : X ⟶ Y) : homOfCocone h (coconeOfHom h f) = f := by
  simp [homOfCocone, coconeOfHom]

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
@[implicit_reducible]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F
  body: coconeOfHom h (𝟙 X)

中文:
定义 colimitCocone
  签名: : 余锥 F
  定义体: coconeOfHom h (𝟙 X)

Depends on / 依赖: coconeOfHom
-/
def colimitCocone : Cocone F :=
  coconeOfHom h (𝟙 X)

/--
theorem `coconeOfHom_fac` / 定理 `coconeOfHom_fac`

English:
theorem coconeOfHom_fac
  given: {Y : C} (f : X ⟶ Y)
  statement: coconeOfHom h f = (colimitCocone h).extend f
  proof: by
  dsimp [coconeOfHom, colimitCocone, Cocone.extend]
  congr
  conv_lhs => rw [← Category.id_comp f]
  exact h.homEquiv_comp f (𝟙 X)

中文:
定理 coconeOfHom_fac
  条件: {Y : C} (f : X ⟶ Y)
  结论: coconeOfHom h f = (colimitCocone h).extend f
  证明: by
  dsimp [coconeOfHom, colimitCocone, Cocone.extend]
  congr
  conv_lhs => rw [← Category.id_comp f]
  exact h.homEquiv_comp f (𝟙 X)

Depends on / 依赖: Category, Category.id_comp, Cocone, Cocone.extend, coconeOfHom, colimitCocone, conv_lhs, extend, h.homEquiv_comp, homEquiv_comp, id_comp
-/
theorem coconeOfHom_fac {Y : C} (f : X ⟶ Y) : coconeOfHom h f = (colimitCocone h).extend f := by
  dsimp [coconeOfHom, colimitCocone, Cocone.extend]
  congr
  conv_lhs => rw [← Category.id_comp f]
  exact h.homEquiv_comp f (𝟙 X)

/--
theorem `cocone_fac` / 定理 `cocone_fac`

English:
theorem cocone_fac
  given: (s : Cocone F)
  statement: (colimitCocone h).extend (homOfCocone h s) = s
  proof: by
  rw [← coconeOfHom_homOfCocone h s]
  conv_lhs => simp only [homOfCocone_coconeOfHom]
  apply (coconeOfHom_fac _ _).symm

中文:
定理 cocone_fac
  条件: (s : 余锥 F)
  结论: (colimitCocone h).extend (homOfCocone h s) = s
  证明: by
  rw [← coconeOfHom_homOfCocone h s]
  conv_lhs => simp only [homOfCocone_coconeOfHom]
  apply (coconeOfHom_fac _ _).symm

Depends on / 依赖: coconeOfHom_fac, coconeOfHom_homOfCocone, conv_lhs, homOfCocone_coconeOfHom
-/
theorem cocone_fac (s : Cocone F) : (colimitCocone h).extend (homOfCocone h s) = s := by
  rw [← coconeOfHom_homOfCocone h s]
  conv_lhs => simp only [homOfCocone_coconeOfHom]
  apply (coconeOfHom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/--
Definition of `ofCorepresentableBy` / `ofCorepresentableBy` 的定义

English:
definition ofCorepresentableBy
  signature: {X : C} (h : F.cocones.CorepresentableBy X)
  body: homOfCocone h s
  fac s j := by
    have h := cocone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCocone_coconeOfHom h m]
    congr
    rw [coconeOfHom_fac]
    dsimp [Cocone.extend]; cases s; congr with j; exa

中文:
定义 ofCorepresentableBy
  签名: {X : C} (h : F.cocones.余representableBy X)
  定义体: homOfCocone h s
  fac s j := by
    have h := cocone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCocone_coconeOfHom h m]
    congr
    rw [coconeOfHom_fac]
    dsimp [Cocone.extend]; cases s; congr with j; exa

Depends on / 依赖: homOfCocone
-/
def ofCorepresentableBy {X : C} (h : F.cocones.CorepresentableBy X) :
    IsColimit (colimitCocone h) where
  desc s := homOfCocone h s
  fac s j := by
    have h := cocone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCocone_coconeOfHom h m]
    congr
    rw [coconeOfHom_fac]
    dsimp [Cocone.extend]; cases s; congr with j; exact w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `corepresentableBy` / `corepresentableBy` 的定义

English:
definition corepresentableBy
  signature: (hc : IsColimit t)
  body: hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

中文:
定义 corepresentableBy
  签名: (hc : 是余极限 t)
  定义体: hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

Depends on / 依赖: hc.homEquiv, homEquiv
-/
def corepresentableBy (hc : IsColimit t) : F.cocones.CorepresentableBy t.pt where
  homEquiv := hc.homEquiv
homEquiv_comp {X X'} f g := NatTrans.ext funext fun j => by simp

end

end IsColimit

end CategoryTheory.Limits
