/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weak limits

If `F : J ⥤ C` is a functor and `c : Cone F`, we say that `c` is a weak limit of `F` if
every cone over `F` admits a (not necessarily unique) morphism to `c`. In other words, a
weak limit satisfies the same "versal property" as a limit, without the uniqueness
condition. In particular, weak limits are not unique, and they are not functorial.

We set up some API for weak limits, mostly copied from that for limits, prove that any
limit cone is a weak limit cone, and that, if a limit exists, then it is a retract of any
weak limit (see `IsWeakLimit.retractOfIsLimit`).

In the files `WeakEqualizers.lean`, `WeakKernels.lean` and `WeakPullbacks.lean`, we specialize
to weak equalizers, weak kernels and weak pullbacks, and give some API for those shapes,
again inspired from the non-weak case. We prove that a category with weak equalizers and
pullbacks has weak pullbacks, and that a preadditive category has weak equalizers if and only
if it has weak kernels.

## References

* [Peter J Freyd, *Representations in Abelian categories*, p. 99][freyd1966repabelian]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

variable {J : Type*} [Category* J] {K : Type*} [Category* K] {C : Type*}
    [Category* C] {F : Functor J C} {D : Type*} [Category* D] {G : Functor K D}

namespace CategoryTheory.Limits

/--
Definition of `IsWeakLimit` / `IsWeakLimit` 的定义

English:
structure IsWeakLimit
  parameters: (t : Cone F)
  axioms and operations (2):
    - lift : forall s : Cone F, s.pt ⟶ t.pt
    - fac : forall (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j  [default: by cat_disch]

中文:
结构 是WeakLimit
  参数: (t : 锥 F)
  公理与运算 (2 个):
    - lift : 对任意 s : 锥 F, s.pt ⟶ t.pt
    - fac : 对任意 (s : 锥 F) (j : J), lift s ≫ t.π.app j = s.π.app j  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsWeakLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : forall s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : forall (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch

attribute [reassoc (attr := simp)] IsWeakLimit.fac

/--
Definition of `IsWeakLimit.retractOfIsLimit` / `IsWeakLimit.retractOfIsLimit` 的定义

English:
definition IsWeakLimit.retractOfIsLimit
  signature: {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t')
  body: l'.lift t
  r := l.lift t'
  retract := l.hom_ext (fun _ => by rw [assoc, id_comp, l.fac t', l'.fac t])

中文:
定义 是WeakLimit.retractOfIsLimit
  签名: {t t' : 锥 F} (l : 是极限 t) (l' : 是WeakLimit t')
  定义体: l'.lift t
  r := l.lift t'
  retract := l.hom_ext (fun _ => by rw [assoc, id_comp, l.fac t', l'.fac t])
-/
def IsWeakLimit.retractOfIsLimit {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t') :
    Retract t.pt t'.pt where
  i := l'.lift t
  r := l.lift t'
  retract := l.hom_ext (fun _ => by rw [assoc, id_comp, l.fac t', l'.fac t])

/--
Definition of `IsLimit.isWeakLimit` / `IsLimit.isWeakLimit` 的定义

English:
definition IsLimit.isWeakLimit
  signature: {t : Cone F} (l : IsLimit t)
  body: l.lift
  fac := l.fac

中文:
定义 是极限.isWeakLimit
  签名: {t : 锥 F} (l : 是极限 t)
  定义体: l.lift
  fac := l.fac

Depends on / 依赖: l.lift
-/
def IsLimit.isWeakLimit {t : Cone F} (l : IsLimit t) : IsWeakLimit t where
  lift := l.lift
  fac := l.fac

/--
Definition of `WeakLimitCone` / `WeakLimitCone` 的定义

English:
structure WeakLimitCone
  parameters: (F : J ⥤ C)
  axioms and operations (2):
    - cone : Cone F
    - isWeakLimit : IsWeakLimit cone

中文:
结构 WeakLimitCone
  参数: (F : J ⥤ C)
  公理与运算 (2 个):
    - cone : 锥 F
    - isWeakLimit : 是WeakLimit cone
-/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the weak limit cone -/
  isWeakLimit : IsWeakLimit cone

/--
Definition of `WeakLimitCone.ofLimitCone` / `WeakLimitCone.ofLimitCone` 的定义

English:
definition WeakLimitCone.ofLimitCone
  signature: {F : J ⥤ C} (c : LimitCone F)
  body: c.cone
  isWeakLimit := c.isLimit.isWeakLimit

中文:
定义 WeakLimitCone.ofLimitCone
  签名: {F : J ⥤ C} (c : 极限锥 F)
  定义体: c.cone
  isWeakLimit := c.isLimit.isWeakLimit

Depends on / 依赖: c.cone
-/
def WeakLimitCone.ofLimitCone {F : J ⥤ C} (c : LimitCone F) : WeakLimitCone F where
  cone := c.cone
  isWeakLimit := c.isLimit.isWeakLimit

/--
Definition of `HasWeakLimit` / `HasWeakLimit` 的定义

English:
class HasWeakLimit
  parameters: (F : J ⥤ C)
  (no additional axioms)

中文:
类 有WeakLimit
  参数: (F : J ⥤ C)
  (无附加公理)

Depends on / 依赖: Functor, Functor.preservesProjectiveObjects_of_isEquivalence, preservesProjectiveObjects_of_isEquivalence
-/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimitCone : Nonempty (WeakLimitCone F)

/--
If `F` has a limit, then it has a weak limit.
-/
instance (F : J ⥤ C) [HasLimit F] : HasWeakLimit F where
  exists_weakLimitCone := Nonempty.intro (WeakLimitCone.ofLimitCone (getLimitCone F))

/--
theorem `HasWeakLimit.mk` / 定理 `HasWeakLimit.mk`

English:
theorem HasWeakLimit.mk
  given: {F : J ⥤ C} (d : WeakLimitCone F)
  statement: HasWeakLimit F
  proof: ⟨Nonempty.intro d⟩

中文:
定理 有WeakLimit.mk
  条件: {F : J ⥤ C} (d : WeakLimitCone F)
  结论: 有WeakLimit F
  证明: ⟨Nonempty.intro d⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasWeakLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
@[no_expose]
/--
Definition of `getWeakLimitCone` / `getWeakLimitCone` 的定义

English:
definition getWeakLimitCone
  signature: (F : J ⥤ C) [HasWeakLimit F]
  body: Classical.choice HasWeakLimit.exists_weakLimitCone

中文:
定义 getWeakLimitCone
  签名: (F : J ⥤ C) [有WeakLimit F]
  定义体: Classical.choice HasWeakLimit.exists_weakLimitCone

Depends on / 依赖: Classical, Classical.choice, HasWeakLimit, HasWeakLimit.exists_weakLimitCone, choice, exists_weakLimitCone
-/
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
Classical.choice HasWeakLimit.exists_weakLimitCone

variable (J C) in
/--
Definition of `HasWeakLimitsOfShape` / `HasWeakLimitsOfShape` 的定义

English:
class HasWeakLimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - hasWeakLimit : forall F : J ⥤ C, HasWeakLimit F  [default: by infer_instance]

中文:
类 有WeakLimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - hasWeakLimit : 对任意 F : J ⥤ C, 有WeakLimit F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  hasWeakLimit : forall F : J ⥤ C, HasWeakLimit F := by infer_instance

attribute [instance] HasWeakLimitsOfShape.hasWeakLimit

instance (priority := 100) [HasLimitsOfShape J C] : HasWeakLimitsOfShape J C where

-- Interface to the `HasWeakLimit` class.
/--
Definition of `weakLimit.cone` / `weakLimit.cone` 的定义

English:
definition weakLimit.cone
  signature: (F : J ⥤ C) [HasWeakLimit F]
  body: (getWeakLimitCone F).cone

中文:
定义 weakLimit.cone
  签名: (F : J ⥤ C) [有WeakLimit F]
  定义体: (getWeakLimitCone F).cone

Depends on / 依赖: getWeakLimitCone
-/
def weakLimit.cone (F : J ⥤ C) [HasWeakLimit F] : Cone F :=
  (getWeakLimitCone F).cone

/--
Definition of `weakLimit` / `weakLimit` 的定义

English:
definition weakLimit
  signature: (F : J ⥤ C) [HasWeakLimit F]
  body: (weakLimit.cone F).pt

中文:
定义 weakLimit
  签名: (F : J ⥤ C) [有WeakLimit F]
  定义体: (weakLimit.cone F).pt

Depends on / 依赖: weakLimit, weakLimit.cone
-/
def weakLimit (F : J ⥤ C) [HasWeakLimit F] :=
  (weakLimit.cone F).pt

/--
Definition of `weakLimit.π` / `weakLimit.π` 的定义

English:
definition weakLimit.π
  signature: (F : J ⥤ C) [HasWeakLimit F] (j : J)
  body: (weakLimit.cone F).π.app j

@[reassoc]

中文:
定义 weakLimit.π
  签名: (F : J ⥤ C) [有WeakLimit F] (j : J)
  定义体: (weakLimit.cone F).π.app j

@[reassoc]

Depends on / 依赖: weakLimit, weakLimit.cone
-/
def weakLimit.π (F : J ⥤ C) [HasWeakLimit F] (j : J) : weakLimit F ⟶ F.obj j :=
  (weakLimit.cone F).π.app j

@[reassoc]
/--
theorem `weakLimit.π_comp_eqToHom` / 定理 `weakLimit.π_comp_eqToHom`

English:
theorem weakLimit.π_comp_eqToHom
  given: (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j')
  proof: by
  subst hj
  simp

@[simp]

中文:
定理 weakLimit.π_comp_eqToHom
  条件: (F : J ⥤ C) [有WeakLimit F] {j j' : J} (hj : j = j')
  证明: by
  subst hj
  simp

@[simp]
-/
theorem weakLimit.π_comp_eqToHom (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j') :
    weakLimit.π F j ≫ eqToHom (by subst hj; rfl) = weakLimit.π F j' := by
  subst hj
  simp

@[simp]
/--
theorem `weakLimit.cone_pt` / 定理 `weakLimit.cone_pt`

English:
theorem weakLimit.cone_pt
  given: {F : J ⥤ C} [HasWeakLimit F]
  proof: rfl

@[simp]

中文:
定理 weakLimit.cone_pt
  条件: {F : J ⥤ C} [有WeakLimit F]
  证明: rfl

@[simp]
-/
theorem weakLimit.cone_pt {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).pt = weakLimit F := rfl

@[simp]
/--
theorem `weakLimit.cone_π` / 定理 `weakLimit.cone_π`

English:
theorem weakLimit.cone_π
  given: {F : J ⥤ C} [HasWeakLimit F]
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 weakLimit.cone_π
  条件: {F : J ⥤ C} [有WeakLimit F]
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem weakLimit.cone_π {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).π.app = weakLimit.π _ := rfl

@[reassoc (attr := simp)]
/--
theorem `weakLimit.w` / 定理 `weakLimit.w`

English:
theorem weakLimit.w
  given: (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j')
  proof: (weakLimit.cone F).w f

中文:
定理 weakLimit.w
  条件: (F : J ⥤ C) [有WeakLimit F] {j j' : J} (f : j ⟶ j')
  证明: (weakLimit.cone F).w f

Depends on / 依赖: P.isColimitCokernelCofork, epi_of_isColimit_cofork, infer_instance, isColimitCokernelCofork, weakLimit, weakLimit.cone
-/
theorem weakLimit.w (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j') :
    weakLimit.π F j ≫ F.map f = weakLimit.π F j' :=
  (weakLimit.cone F).w f

/--
Definition of `weakLimit.isWeakLimit` / `weakLimit.isWeakLimit` 的定义

English:
definition weakLimit.isWeakLimit
  signature: (F : J ⥤ C) [HasWeakLimit F]
  body: (getWeakLimitCone F).isWeakLimit

中文:
定义 weakLimit.isWeakLimit
  签名: (F : J ⥤ C) [有WeakLimit F]
  定义体: (getWeakLimitCone F).isWeakLimit

Depends on / 依赖: getWeakLimitCone, isWeakLimit
-/
def weakLimit.isWeakLimit (F : J ⥤ C) [HasWeakLimit F] :
    IsWeakLimit (weakLimit.cone F) :=
  (getWeakLimitCone F).isWeakLimit

/--
Definition of `weakLimit.lift` / `weakLimit.lift` 的定义

English:
definition weakLimit.lift
  signature: (F : J ⥤ C) [HasWeakLimit F] (c : Cone F)
  body: (weakLimit.isWeakLimit F).lift c

@[simp]

中文:
定义 weakLimit.lift
  签名: (F : J ⥤ C) [有WeakLimit F] (c : 锥 F)
  定义体: (weakLimit.isWeakLimit F).lift c

@[simp]

Depends on / 依赖: isWeakLimit, weakLimit, weakLimit.isWeakLimit
-/
def weakLimit.lift (F : J ⥤ C) [HasWeakLimit F] (c : Cone F) :
    c.pt ⟶ weakLimit F :=
  (weakLimit.isWeakLimit F).lift c

@[simp]
/--
theorem `weakLimit.isWeakLimit_lift` / 定理 `weakLimit.isWeakLimit_lift`

English:
theorem weakLimit.isWeakLimit_lift
  given: {F : J ⥤ C} [HasWeakLimit F] (c : Cone F)
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 weakLimit.isWeakLimit_lift
  条件: {F : J ⥤ C} [有WeakLimit F] (c : 锥 F)
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem weakLimit.isWeakLimit_lift {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) :
    (weakLimit.isWeakLimit F).lift c = weakLimit.lift F c :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `weakLimit.lift_π` / 定理 `weakLimit.lift_π`

English:
theorem weakLimit.lift_π
  given: {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J)
  proof: IsWeakLimit.fac _ c j

中文:
定理 weakLimit.lift_π
  条件: {F : J ⥤ C} [有WeakLimit F] (c : 锥 F) (j : J)
  证明: IsWeakLimit.fac _ c j

Depends on / 依赖: IsWeakLimit, IsWeakLimit.fac
-/
theorem weakLimit.lift_π {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J) :
    weakLimit.lift F c ≫ weakLimit.π F j = c.π.app j :=
  IsWeakLimit.fac _ c j

namespace IsWeakLimit

/-- Transport evidence that a cone is a weak limit cone across an isomorphism of cones. -/
@[simps]
/--
Definition of `ofIsoWeakLimit` / `ofIsoWeakLimit` 的定义

English:
definition ofIsoWeakLimit
  signature: {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t)
  body: P.lift s ≫ i.hom.hom

中文:
定义 ofIsoWeakLimit
  签名: {r t : 锥 F} (P : 是WeakLimit r) (i : r ≅ t)
  定义体: P.lift s ≫ i.hom.hom

Depends on / 依赖: P.lift, i.hom.hom
-/
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom

/--
Definition of `equivIsoWeakLimit` / `equivIsoWeakLimit` 的定义

English:
definition equivIsoWeakLimit
  signature: {r t : Cone F} (i : r ≅ t)
  body: h.ofIsoWeakLimit i
  invFun h := h.ofIsoWeakLimit i.symm
  left_inv _ := by simp [ofIsoWeakLimit]
  right_inv _ := by simp [ofIsoWeakLimit]

@[simp]

中文:
定义 equivIsoWeakLimit
  签名: {r t : 锥 F} (i : r ≅ t)
  定义体: h.ofIsoWeakLimit i
  invFun h := h.ofIsoWeakLimit i.symm
  left_inv _ := by simp [ofIsoWeakLimit]
  right_inv _ := by simp [ofIsoWeakLimit]

@[simp]

Depends on / 依赖: h.ofIsoWeakLimit, ofIsoWeakLimit
-/
def equivIsoWeakLimit {r t : Cone F} (i : r ≅ t) : IsWeakLimit r ≃ IsWeakLimit t where
  toFun h := h.ofIsoWeakLimit i
  invFun h := h.ofIsoWeakLimit i.symm
  left_inv _ := by simp [ofIsoWeakLimit]
  right_inv _ := by simp [ofIsoWeakLimit]

@[simp]
/--
theorem `equivIsoWeakLimit_apply` / 定理 `equivIsoWeakLimit_apply`

English:
theorem equivIsoWeakLimit_apply
  given: {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit r)
  proof: rfl

@[simp]

中文:
定理 equivIsoWeakLimit_apply
  条件: {r t : 锥 F} (i : r ≅ t) (P : 是WeakLimit r)
  证明: rfl

@[simp]
-/
theorem equivIsoWeakLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit r) :
    equivIsoWeakLimit i P = P.ofIsoWeakLimit i :=
  rfl

@[simp]
/--
theorem `equivIsoWeakLimit_symm_apply` / 定理 `equivIsoWeakLimit_symm_apply`

English:
theorem equivIsoWeakLimit_symm_apply
  given: {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit t)
  proof: rfl

中文:
定理 equivIsoWeakLimit_symm_apply
  条件: {r t : 锥 F} (i : r ≅ t) (P : 是WeakLimit t)
  证明: rfl
-/
theorem equivIsoWeakLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit t) :
    (equivIsoWeakLimit i).symm P = P.ofIsoWeakLimit i.symm :=
  rfl

/-- The versal morphism from any other cone to a weak limit cone. -/
@[simps]
/--
Definition of `liftConeMorphism` / `liftConeMorphism` 的定义

English:
definition liftConeMorphism
  signature: {t : Cone F} (h : IsWeakLimit t) (s : Cone F)
  body: h.lift s

中文:
定义 liftConeMorphism
  签名: {t : 锥 F} (h : 是WeakLimit t) (s : 锥 F)
  定义体: h.lift s

Depends on / 依赖: h.lift
-/
def liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

/-- Alternative constructor for `isWeakLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
/--
Definition of `mkOfConeMorphism` / `mkOfConeMorphism` 的定义

English:
definition mkOfConeMorphism
  signature: {t : Cone F} (lift : forall s : Cone F, s ⟶ t)
  body: (lift s).hom

中文:
定义 mkOfConeMorphism
  签名: {t : 锥 F} (lift : 对任意 s : 锥 F, s ⟶ t)
  定义体: (lift s).hom
-/
def mkOfConeMorphism {t : Cone F} (lift : forall s : Cone F, s ⟶ t) : IsWeakLimit t where
  lift s := (lift s).hom

/--
Definition of `ofRightAdjoint` / `ofRightAdjoint` 的定义

English:
definition ofRightAdjoint
  signature: {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
  body: mkOfConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))

中文:
定义 ofRightAdjoint
  签名: {left : 锥 F ⥤ 锥 G} {right : 锥 G ⥤ 锥 F}
  定义体: mkOfConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))

Depends on / 依赖: adj.homEquiv, homEquiv, liftConeMorphism, mkOfConeMorphism, t.liftConeMorphism
-/
def ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c) :=
  mkOfConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))

/--
lemma `iff_of_cone_equiv` / 引理 `iff_of_cone_equiv`

English:
lemma iff_of_cone_equiv
  given: {D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G}
  proof: ⟨fun P => Nonempty.intro (IsWeakLimit.ofIsoWeakLimit
    (IsWeakLimit.ofRightAdjoint h.toAdjunction P.some) (h.unitIso.symm.app c)),
   fun P => Nonempty.intro (IsWeakLimit.ofRightAdjoint h.symm.toAdjunction P.some)⟩

中文:
引理 iff_of_cone_equiv
  条件: {D : 类型} [范畴* D] {G : K ⥤ D} (h : 锥 G ≌ 锥 F) {c : 锥 G}
  证明: ⟨fun P => Nonempty.intro (IsWeakLimit.ofIsoWeakLimit
    (IsWeakLimit.ofRightAdjoint h.toAdjunction P.some) (h.unitIso.symm.app c)),
   fun P => Nonempty.intro (IsWeakLimit.ofRightAdjoint h.symm.toAdjunction P.some)⟩

Depends on / 依赖: IsWeakLimit, IsWeakLimit.ofIsoWeakLimit, IsWeakLimit.ofRightAdjoint, Nonempty, Nonempty.intro, P.some, h.symm.toAdjunction, h.toAdjunction, h.unitIso.symm.app, ofIsoWeakLimit, ofRightAdjoint, toAdjunction, unitIso
-/
lemma iff_of_cone_equiv {D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    Nonempty (IsWeakLimit (h.functor.obj c)) ↔ Nonempty (IsWeakLimit c) :=
  ⟨fun P => Nonempty.intro (IsWeakLimit.ofIsoWeakLimit
    (IsWeakLimit.ofRightAdjoint h.toAdjunction P.some) (h.unitIso.symm.app c)),
   fun P => Nonempty.intro (IsWeakLimit.ofRightAdjoint h.symm.toAdjunction P.some)⟩

/--
lemma `postcompose_hom_iff_of_iso` / 引理 `postcompose_hom_iff_of_iso`

English:
lemma postcompose_hom_iff_of_iso
  given: {F G : J ⥤ C} (α : F ≅ G) (c : Cone F)
  proof: iff_of_cone_equiv (Cone.postcomposeEquivalence α)

中文:
引理 postcompose_hom_iff_of_iso
  条件: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 F)
  证明: iff_of_cone_equiv (Cone.postcomposeEquivalence α)

Depends on / 依赖: Cone.postcomposeEquivalence, iff_of_cone_equiv, postcomposeEquivalence
-/
lemma postcompose_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  iff_of_cone_equiv (Cone.postcomposeEquivalence α)

/--
lemma `postcompose_inv_iff_of_iso` / 引理 `postcompose_inv_iff_of_iso`

English:
lemma postcompose_inv_iff_of_iso
  given: {F G : J ⥤ C} (α : F ≅ G) (c : Cone G)
  proof: postcompose_hom_iff_of_iso α.symm c

中文:
引理 postcompose_inv_iff_of_iso
  条件: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 G)
  证明: postcompose_hom_iff_of_iso α.symm c

Depends on / 依赖: postcompose_hom_iff_of_iso
-/
lemma postcompose_inv_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.inv).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  postcompose_hom_iff_of_iso α.symm c

/--
lemma `iff_of_natIso_of_iso` / 引理 `iff_of_natIso_of_iso`

English:
lemma iff_of_natIso_of_iso
  statement: {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
  proof: (postcompose_hom_iff_of_iso α _).symm.trans (IsWeakLimit.equivIsoWeakLimit w).nonempty_congr

中文:
引理 iff_of_natIso_of_iso
  结论: {F G : J ⥤ C} (α : F ≅ G) (c : 锥 F) (d : 锥 G)
  证明: (postcompose_hom_iff_of_iso α _).symm.trans (IsWeakLimit.equivIsoWeakLimit w).nonempty_congr

Depends on / 依赖: IsWeakLimit, IsWeakLimit.equivIsoWeakLimit, equivIsoWeakLimit, nonempty_congr, postcompose_hom_iff_of_iso, symm.trans
-/
lemma iff_of_natIso_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
    (w : (Cone.postcompose α.hom).obj c ≅ d) :
    Nonempty (IsWeakLimit c) ↔ Nonempty (IsWeakLimit d) :=
  (postcompose_hom_iff_of_iso α _).symm.trans (IsWeakLimit.equivIsoWeakLimit w).nonempty_congr

end IsWeakLimit

/--
theorem `hasWeakLimit_of_iso` / 定理 `hasWeakLimit_of_iso`

English:
theorem hasWeakLimit_of_iso
  given: {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G)
  statement: HasWeakLimit G
  proof: HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit :=
        Nonempty.some ((IsWeakLimit.postcompose_hom_iff_of_iso α _ ).mpr
        (Nonempty.intro (weakLimit.isWeakLimit F))) }

中文:
定理 hasWeakLimit_of_iso
  条件: {F G : J ⥤ C} [有WeakLimit F] (α : F ≅ G)
  结论: 有WeakLimit G
  证明: HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit :=
        Nonempty.some ((IsWeakLimit.postcompose_hom_iff_of_iso α _ ).mpr
        (Nonempty.intro (weakLimit.isWeakLimit F))) }

Depends on / 依赖: Cone.postcompose, HasWeakLimit, HasWeakLimit.mk, IsWeakLimit, IsWeakLimit.postcompose_hom_iff_of_iso, Nonempty, Nonempty.intro, Nonempty.some, isWeakLimit, postcompose, postcompose_hom_iff_of_iso, weakLimit, weakLimit.cone, weakLimit.isWeakLimit
-/
theorem hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G :=
  HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit :=
        Nonempty.some ((IsWeakLimit.postcompose_hom_iff_of_iso α _ ).mpr
        (Nonempty.intro (weakLimit.isWeakLimit F))) }

/--
theorem `hasWeakLimit_iff_of_iso` / 定理 `hasWeakLimit_iff_of_iso`

English:
theorem hasWeakLimit_iff_of_iso
  given: {F G : J ⥤ C} (α : F ≅ G)
  statement: HasWeakLimit F ↔ HasWeakLimit G
  proof: ⟨fun _ => hasWeakLimit_of_iso α, fun _ => hasWeakLimit_of_iso α.symm⟩

中文:
定理 hasWeakLimit_iff_of_iso
  条件: {F G : J ⥤ C} (α : F ≅ G)
  结论: 有WeakLimit F ↔ 有WeakLimit G
  证明: ⟨fun _ => hasWeakLimit_of_iso α, fun _ => hasWeakLimit_of_iso α.symm⟩

Depends on / 依赖: hasWeakLimit_of_iso
-/
theorem hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWeakLimit G :=
  ⟨fun _ => hasWeakLimit_of_iso α, fun _ => hasWeakLimit_of_iso α.symm⟩

end CategoryTheory.Limits
