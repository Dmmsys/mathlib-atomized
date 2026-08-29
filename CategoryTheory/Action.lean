/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Actions as functors and as categories

From a multiplicative action M ↻ X, we can construct a functor from M to the category of
types, mapping the single object of M to X and an element `m : M` to the map `X → X` given by
multiplication by `m`.
  This functor induces a category structure on X -- a special case of the category of elements.
A morphism `x ⟶ y` in this category is simply a scalar `m : M` such that `m • x = y`. In the case
where M is a group, this category is a groupoid -- the *action groupoid*.
-/

@[expose] public section


open MulAction SemidirectProduct

namespace CategoryTheory

universe u

variable (M : Type*) [Monoid M] (X : Type u) [MulAction M X]

/-- A multiplicative action M ↻ X viewed as a functor mapping the single object of M to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`. -/
@[simps obj map]
/--
Definition of `actionAsFunctor` / `actionAsFunctor` 的定义

English:
definition actionAsFunctor
  signature: : SingleObj M ⥤ Type u where
  body: X
  map f := ↾(f • ·)
  map_id _ := by ext; exact MulAction.one_smul _
  map_comp f g := by ext x; exact (smul_smul g f x).symm

中文:
定义 actionAsFunctor
  签名: : SingleObj M ⥤ 类型u where
  定义体: X
  map f := ↾(f • ·)
  map_id _ := by ext; exact MulAction.one_smul _
  map_comp f g := by ext x; exact (smul_smul g f x).symm
-/
def actionAsFunctor : SingleObj M ⥤ Type u where
  obj _ := X
  map f := ↾(f • ·)
  map_id _ := by ext; exact MulAction.one_smul _
  map_comp f g := by ext x; exact (smul_smul g f x).symm

/--
Definition of `ActionCategory` / `ActionCategory` 的定义

English:
definition ActionCategory
  body: (actionAsFunctor M X).Elements
deriving Category

中文:
定义 ActionCategory
  定义体: (actionAsFunctor M X).Elements
deriving Category

Depends on / 依赖: Elements, actionAsFunctor
-/
def ActionCategory :=
  (actionAsFunctor M X).Elements
deriving Category

namespace ActionCategory

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : ActionCategory M X ⥤ SingleObj M
  body: CategoryOfElements.π _

@[simp]

中文:
定义 π
  签名: : ActionCategory M X ⥤ SingleObj M
  定义体: CategoryOfElements.π _

@[simp]

Depends on / 依赖: CategoryOfElements
-/
def π : ActionCategory M X ⥤ SingleObj M :=
  CategoryOfElements.π _

@[simp]
/--
theorem `π_map` / 定理 `π_map`

English:
theorem π_map
  given: (p q : ActionCategory M X) (f : p ⟶ q)
  statement: (π M X).map f = f.val
  proof: rfl

@[simp]

中文:
定理 π_map
  条件: (p q : ActionCategory M X) (f : p ⟶ q)
  结论: (π M X).map f = f.val
  证明: rfl

@[simp]
-/
theorem π_map (p q : ActionCategory M X) (f : p ⟶ q) : (π M X).map f = f.val :=
  rfl

@[simp]
/--
theorem `π_obj` / 定理 `π_obj`

English:
theorem π_obj
  given: (p : ActionCategory M X)
  statement: (π M X).obj p = SingleObj.star M
  proof: Unit.ext _ _

中文:
定理 π_obj
  条件: (p : ActionCategory M X)
  结论: (π M X).obj p = SingleObj.star M
  证明: Unit.ext _ _

Depends on / 依赖: Unit.ext
-/
theorem π_obj (p : ActionCategory M X) : (π M X).obj p = SingleObj.star M :=
  Unit.ext _ _

variable {M X}

/--
Definition of `back` / `back` 的定义

English:
definition back
  signature: : ActionCategory M X -> X
  body: fun x => x.snd

中文:
定义 back
  签名: : ActionCategory M X -> X
  定义体: fun x => x.snd
-/
protected def back : ActionCategory M X -> X := fun x => x.snd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC X (ActionCategory M X)
  body: ⟨fun x => ⟨(), x⟩⟩

@[simp]

中文:
实例 :
  签名: CoeTC X (ActionCategory M X)
  定义体: ⟨fun x => ⟨(), x⟩⟩

@[simp]
-/
instance : CoeTC X (ActionCategory M X) :=
  ⟨fun x => ⟨(), x⟩⟩

@[simp]
/--
theorem `coe_back` / 定理 `coe_back`

English:
theorem coe_back
  given: (x : X)
  statement: ActionCategory.back (x : ActionCategory M X) = x
  proof: rfl

@[simp]

中文:
定理 coe_back
  条件: (x : X)
  结论: ActionCategory.back (x : ActionCategory M X) = x
  证明: rfl

@[simp]
-/
theorem coe_back (x : X) : ActionCategory.back (x : ActionCategory M X) = x :=
  rfl

@[simp]
/--
theorem `back_coe` / 定理 `back_coe`

English:
theorem back_coe
  given: (x : ActionCategory M X)
  statement: ↑x.back = x
  proof: by cases x; rfl

中文:
定理 back_coe
  条件: (x : ActionCategory M X)
  结论: ↑x.back = x
  证明: by cases x; rfl
-/
theorem back_coe (x : ActionCategory M X) : ↑x.back = x := by cases x; rfl

variable (M X)

/--
Definition of `objEquiv` / `objEquiv` 的定义

English:
definition objEquiv
  signature: : X ≃ ActionCategory M X where
  body: x
  invFun x := x.back
  left_inv := coe_back
  right_inv := back_coe

中文:
定义 objEquiv
  签名: : X ≃ ActionCategory M X where
  定义体: x
  invFun x := x.back
  left_inv := coe_back
  right_inv := back_coe
-/
def objEquiv : X ≃ ActionCategory M X where
  toFun x := x
  invFun x := x.back
  left_inv := coe_back
  right_inv := back_coe

/--
theorem `hom_as_subtype` / 定理 `hom_as_subtype`

English:
theorem hom_as_subtype
  given: (p q : ActionCategory M X)
  statement: (p ⟶ q) = { m : M // m • p.back = q.back }
  proof: rfl

中文:
定理 hom_as_subtype
  条件: (p q : ActionCategory M X)
  结论: (p ⟶ q) = { m : M // m • p.back = q.back }
  证明: rfl
-/
theorem hom_as_subtype (p q : ActionCategory M X) : (p ⟶ q) = { m : M // m • p.back = q.back } :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: X] : Inhabited (ActionCategory M X)
  body: ⟨show X from default⟩

中文:
实例 [Inhabited
  签名: X] : Inhabited (ActionCategory M X)
  定义体: ⟨show X from default⟩
-/
instance [Inhabited X] : Inhabited (ActionCategory M X) :=
  ⟨show X from default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty (ActionCategory M X)
  body: Nonempty.map (objEquiv M X) inferInstance

中文:
实例 [Nonempty
  签名: X] : Nonempty (ActionCategory M X)
  定义体: Nonempty.map (objEquiv M X) inferInstance

Depends on / 依赖: Nonempty, Nonempty.map, objEquiv
-/
instance [Nonempty X] : Nonempty (ActionCategory M X) :=
  Nonempty.map (objEquiv M X) inferInstance

variable {X} (x : X)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `stabilizerIsoEnd` / `stabilizerIsoEnd` 的定义

English:
definition stabilizerIsoEnd
  signature: : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ x
  body: MulEquiv.refl _

@[simp]

中文:
定义 stabilizerIsoEnd
  签名: : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ x
  定义体: MulEquiv.refl _

@[simp]

Depends on / 依赖: MulEquiv, MulEquiv.refl
-/
def stabilizerIsoEnd : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ x :=
  MulEquiv.refl _

@[simp]
/--
theorem `stabilizerIsoEnd_apply` / 定理 `stabilizerIsoEnd_apply`

English:
theorem stabilizerIsoEnd_apply
  given: (f : stabilizerSubmonoid M x)
  proof: rfl

中文:
定理 stabilizerIsoEnd_apply
  条件: (f : stabilizerSubmonoid M x)
  证明: rfl
-/
theorem stabilizerIsoEnd_apply (f : stabilizerSubmonoid M x) :
    (stabilizerIsoEnd M x) f = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp 1100]
/--
theorem `stabilizerIsoEnd_symm_apply` / 定理 `stabilizerIsoEnd_symm_apply`

English:
theorem stabilizerIsoEnd_symm_apply
  given: (f : End _)
  statement: (stabilizerIsoEnd M x).symm f = f
  proof: rfl

中文:
定理 stabilizerIsoEnd_symm_apply
  条件: (f : End _)
  结论: (stabilizerIsoEnd M x).symm f = f
  证明: rfl
-/
theorem stabilizerIsoEnd_symm_apply (f : End _) : (stabilizerIsoEnd M x).symm f = f :=
  rfl

variable {M}

@[simp]
/--
theorem `id_val` / 定理 `id_val`

English:
theorem id_val
  given: (x : ActionCategory M X)
  statement: Subtype.val (𝟙 x) = 1
  proof: rfl

@[simp]

中文:
定理 id_val
  条件: (x : ActionCategory M X)
  结论: Subtype.val (𝟙 x) = 1
  证明: rfl

@[simp]
-/
protected theorem id_val (x : ActionCategory M X) : Subtype.val (𝟙 x) = 1 :=
  rfl

@[simp]
/--
theorem `comp_val` / 定理 `comp_val`

English:
theorem comp_val
  given: {x y z : ActionCategory M X} (f : x ⟶ y) (g : y ⟶ z)
  proof: rfl

中文:
定理 comp_val
  条件: {x y z : ActionCategory M X} (f : x ⟶ y) (g : y ⟶ z)
  证明: rfl
-/
protected theorem comp_val {x y z : ActionCategory M X} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = g.val * f.val :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPretransitive
  signature: M X] [Nonempty X] : IsConnected (ActionCategory M X)
  body: zigzag_isConnected fun x y =>
Relation.ReflTransGen.single
Or.inl nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)

中文:
实例 [IsPretransitive
  签名: M X] [Nonempty X] : IsConnected (ActionCategory M X)
  定义体: zigzag_isConnected fun x y =>
Relation.ReflTransGen.single
Or.inl nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)

Depends on / 依赖: Or.inl, ReflTransGen, Relation, Relation.ReflTransGen.single, exists_smul_eq, nonempty_subtype, nonempty_subtype.mpr, single, x.back, y.back, zigzag_isConnected
-/
instance [IsPretransitive M X] [Nonempty X] : IsConnected (ActionCategory M X) :=
  zigzag_isConnected fun x y =>
Relation.ReflTransGen.single
Or.inl nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)

section Group

variable {G : Type*} [Group G] [MulAction G X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Groupoid (ActionCategory G X)
  body: CategoryTheory.groupoidOfElements _

中文:
实例 :
  签名: Groupoid (ActionCategory G X)
  定义体: CategoryTheory.groupoidOfElements _

Depends on / 依赖: CategoryTheory, CategoryTheory.groupoidOfElements, groupoidOfElements
-/
instance : Groupoid (ActionCategory G X) :=
  CategoryTheory.groupoidOfElements _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `endMulEquivSubgroup` / `endMulEquivSubgroup` 的定义

English:
definition endMulEquivSubgroup
  signature: (H : Subgroup G)
  body: MulEquiv.trans (stabilizerIsoEnd G ((1 : G) : G ⧸ H)).symm
    (MulEquiv.subgroupCongr <| stabilizer_quotient H)

中文:
定义 endMulEquivSubgroup
  签名: (H : Subgroup G)
  定义体: MulEquiv.trans (stabilizerIsoEnd G ((1 : G) : G ⧸ H)).symm
    (MulEquiv.subgroupCongr <| stabilizer_quotient H)

Depends on / 依赖: MulEquiv, MulEquiv.subgroupCongr, MulEquiv.trans, stabilizerIsoEnd, stabilizer_quotient, subgroupCongr
-/
def endMulEquivSubgroup (H : Subgroup G) : End (objEquiv G (G ⧸ H) ↑(1 : G)) ≃* H :=
  MulEquiv.trans (stabilizerIsoEnd G ((1 : G) : G ⧸ H)).symm
    (MulEquiv.subgroupCongr <| stabilizer_quotient H)

/--
Definition of `homOfPair` / `homOfPair` 的定义

English:
definition homOfPair
  signature: (t : X) (g : G)
  body: Subtype.mk g (smul_inv_smul g t)

@[simp]

中文:
定义 homOfPair
  签名: (t : X) (g : G)
  定义体: Subtype.mk g (smul_inv_smul g t)

@[simp]

Depends on / 依赖: Subtype, Subtype.mk, smul_inv_smul
-/
def homOfPair (t : X) (g : G) : @Quiver.Hom (ActionCategory G X) _ (g⁻¹ • t :) t :=
  Subtype.mk g (smul_inv_smul g t)

@[simp]
/--
theorem `homOfPair.val` / 定理 `homOfPair.val`

English:
theorem homOfPair.val
  given: (t : X) (g : G)
  statement: (homOfPair t g).val = g
  proof: rfl

中文:
定理 homOfPair.val
  条件: (t : X) (g : G)
  结论: (homOfPair t g).val = g
  证明: rfl
-/
theorem homOfPair.val (t : X) (g : G) : (homOfPair t g).val = g :=
  rfl

/--
Definition of `cases` / `cases` 的定义

English:
definition cases
  signature: {P : forall ⦃a b : ActionCategory G X⦄, (a ⟶ b) -> Sort*}
  body: by
  refine cast ?_ (hyp b.back f.val)
  rcases a with ⟨⟨⟩, a : X⟩
  rcases b with ⟨⟨⟩, b : X⟩
  rcases f with ⟨g : G, h : g • a = b⟩
  cases inv_smul_eq_iff.mpr h.symm
  rfl

中文:
定义 cases
  签名: {P : 对任意 ⦃a b : ActionCategory G X⦄, (a ⟶ b) -> Sort*}
  定义体: by
  refine cast ?_ (hyp b.back f.val)
  rcases a with ⟨⟨⟩, a : X⟩
  rcases b with ⟨⟨⟩, b : X⟩
  rcases f with ⟨g : G, h : g • a = b⟩
  cases inv_smul_eq_iff.mpr h.symm
  rfl
-/
protected def cases {P : forall ⦃a b : ActionCategory G X⦄, (a ⟶ b) -> Sort*}
    (hyp : forall t g, P (homOfPair t g)) ⦃a b⦄ (f : a ⟶ b) : P f := by
  refine cast ?_ (hyp b.back f.val)
  rcases a with ⟨⟨⟩, a : X⟩
  rcases b with ⟨⟨⟩, b : X⟩
  rcases f with ⟨g : G, h : g • a = b⟩
  cases inv_smul_eq_iff.mpr h.symm
  rfl

variable {H : Type*} [Group H]

set_option backward.defeqAttrib.useBackward true in
/-- Given `G` acting on `X`, a functor from the corresponding action groupoid to a group `H`
can be curried to a group homomorphism `G →* (X → H) ⋊ G`. -/
@[simps]
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (F : ActionCategory G X ⥤ SingleObj H)
  body: have F_map_eq : forall {a b} {f : a ⟶ b}, F.map f = (F.map (homOfPair b.back f.val) : H) := by
    apply ActionCategory.cases
    intros
    rfl
  { toFun := fun g => ⟨fun b => F.map (homOfPair b g), g⟩
    map_one' := by
      dsimp
      ext1
      · ext b
        exact F_map_eq.symm.trans (F.map_

中文:
定义 curry
  签名: (F : ActionCategory G X ⥤ SingleObj H)
  定义体: have F_map_eq : forall {a b} {f : a ⟶ b}, F.map f = (F.map (homOfPair b.back f.val) : H) := by
    apply ActionCategory.cases
    intros
    rfl
  { toFun := fun g => ⟨fun b => F.map (homOfPair b g), g⟩
    map_one' := by
      dsimp
      ext1
      · ext b
        exact F_map_eq.symm.trans (F.map_

Depends on / 依赖: ActionCategory, ActionCategory.cases, F.map, F.map_comp, F.map_id, F_map_eq, F_map_eq.symm.trans, b.back, f.val, homOfPair, intros, map_comp, map_id, map_mul, map_one
-/
def curry (F : ActionCategory G X ⥤ SingleObj H) : G ->* (X -> H) ⋊[mulAutArrow] G :=
  have F_map_eq : forall {a b} {f : a ⟶ b}, F.map f = (F.map (homOfPair b.back f.val) : H) := by
    apply ActionCategory.cases
    intros
    rfl
  { toFun := fun g => ⟨fun b => F.map (homOfPair b g), g⟩
    map_one' := by
      dsimp
      ext1
      · ext b
        exact F_map_eq.symm.trans (F.map_id b)
      rfl
    map_mul' := by
      intro g h
      ext b
      · exact F_map_eq.symm.trans (F.map_comp (homOfPair (g⁻¹ • b) h) (homOfPair b g))
      rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `G` acting on `X`, a group homomorphism `φ : G →* (X → H) ⋊ G` can be uncurried to
a functor from the action groupoid to `H`, provided that `φ g = (_, g)` for all `g`. -/
@[simps]
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: (F : G ->* (X -> H) ⋊[mulAutArrow] G) (sane : forall g, (F g).right = g)
  body: ()
  map {_ b} f := (F f.val).left b.back
  map_id x := by
    dsimp
    rw [F.map_one]
    rfl
  map_comp f g := by
    cases g using ActionCategory.cases
    simp [SingleObj.comp_as_mul, sane]
    rfl

中文:
定义 uncurry
  签名: (F : G ->* (X -> H) ⋊[mulAutArrow] G) (sane : 对任意 g, (F g).right = g)
  定义体: ()
  map {_ b} f := (F f.val).left b.back
  map_id x := by
    dsimp
    rw [F.map_one]
    rfl
  map_comp f g := by
    cases g using ActionCategory.cases
    simp [SingleObj.comp_as_mul, sane]
    rfl
-/
def uncurry (F : G ->* (X -> H) ⋊[mulAutArrow] G) (sane : forall g, (F g).right = g) :
    ActionCategory G X ⥤ SingleObj H where
  obj _ := ()
  map {_ b} f := (F f.val).left b.back
  map_id x := by
    dsimp
    rw [F.map_one]
    rfl
  map_comp f g := by
    cases g using ActionCategory.cases
    simp [SingleObj.comp_as_mul, sane]
    rfl

end Group

end ActionCategory

end CategoryTheory
