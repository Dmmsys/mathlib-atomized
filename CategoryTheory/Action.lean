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
/-
**CategoryTheory.actionAsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：actionAsFunctor : SingleObj M ⥤ Type u where obj _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action M ↻ X viewed as a functor mapping the single object of M
 to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`.
-/
def actionAsFunctor : SingleObj M ⥤ Type u where
  obj _ := X
  map f := ↾(f • ·)
  map_id _ := by ext; exact MulAction.one_smul _
  map_comp f g := by ext x; exact (smul_smul g f x).symm

/-- A multiplicative action M ↻ X induces a category structure on X, where a morphism
from x to y is a scalar taking x to y. Due to implementation details, the object type
of this category is not equal to X, but is in bijection with X. -/
/-
**CategoryTheory.ActionCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ActionCategory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action M ↻ X induces a category structure on X, where a morphis
m
from x to y is a scalar taking x to y. Due to implementation details, the object
 type
of this category is not equal to X, but is in bijection with X.
-/
def ActionCategory :=
  (actionAsFunctor M X).Elements
deriving Category

namespace ActionCategory

/-- The projection from the action category to the monoid, mapping a morphism to its
  label. -/
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the action category to the monoid, mapping a morphism to its
  label.
-/
def π : ActionCategory M X ⥤ SingleObj M :=
  CategoryOfElements.π _

@[simp]
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_map (p q : ActionCategory M X) (f : p ⟶ q) : (π M X).map f = f.val :=
  rfl

@[simp]
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_obj (p : ActionCategory M X) : (π M X).obj p = SingleObj.star M :=
  Unit.ext _ _

variable {M X}

/-- The canonical map `ActionCategory M X → X`. It is given by `fun x => x.snd`, but
  has a more explicit type. -/
/-
**CategoryTheory.ActionCategory.back** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
ctionCategory`。
形式化陈述：{M : Type u_1} → [inst : Monoid M] → {X : Type u} → [inst_1 : MulAction M 
X] → CategoryTheory.ActionCategory M X → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `ActionCategory M X → X`. It is given by `fun x => x.snd`, but
  has a more explicit type.
-/
protected def back : ActionCategory M X → X := fun x => x.snd
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC X (ActionCategory M X) :=
  ⟨fun x => ⟨(), x⟩⟩

@[simp]
/-
**CategoryTheory.ActionCategory.coe_back** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ActionCategory`。
形式化陈述：coe_back (x : X) : ActionCategory.back (x : ActionCategory M X) = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_back (x : X) : ActionCategory.back (x : ActionCategory M X) = x :=
  rfl

@[simp]
/-
**CategoryTheory.ActionCategory.back_coe** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ActionCategory`。
形式化陈述：back_coe (x : ActionCategory M X) : ↑x.back = x
参数：x : ActionCategory M X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem back_coe (x : ActionCategory M X) : ↑x.back = x := by cases x; rfl

variable (M X)

/-- An object of the action category given by M ↻ X corresponds to an element of X. -/
/-
**CategoryTheory.ActionCategory.objEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ActionCategory`。
形式化陈述：objEquiv : X ≃ ActionCategory M X where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ActionCategory.coe_back`：coe_back (x : X) : ActionCategor
y.back (x : ActionCategory M X) = x
· 使用定理 `CategoryTheory.ActionCategory.back_coe`：back_coe (x : ActionCategory M X
) : ↑x.back = x

--- 原说明 ---
An object of the action category given by M ↻ X corresponds to an element of X.
-/
def objEquiv : X ≃ ActionCategory M X where
  toFun x := x
  invFun x := x.back
  left_inv := coe_back
  right_inv := back_coe
/-
**CategoryTheory.ActionCategory.hom_as_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ActionCategory`。
形式化陈述：hom_as_subtype (p q : ActionCategory M X) : (p ⟶ q) = { m : M // m • p.bac
k = q.back }
参数：p q : ActionCategory M X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_as_subtype (p q : ActionCategory M X) : (p ⟶ q) = { m : M // m • p.back = q.back } :=
  rfl
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited X] : Inhabited (ActionCategory M X) :=
  ⟨show X from default⟩
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty X] : Nonempty (ActionCategory M X) :=
  Nonempty.map (objEquiv M X) inferInstance

variable {X} (x : X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent. -/
/-
**CategoryTheory.ActionCategory.stabilizerIsoEnd** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ActionCategory`。
形式化陈述：stabilizerIsoEnd : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ 
x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent.
-/
def stabilizerIsoEnd : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ x :=
  MulEquiv.refl _

@[simp]
/-
**CategoryTheory.ActionCategory.stabilizerIsoEnd_apply** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ActionCategory`。
形式化陈述：stabilizerIsoEnd_apply (f : stabilizerSubmonoid M x) : (stabilizerIsoEnd M
 x) f = f
参数：f : stabilizerSubmonoid M x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stabilizerIsoEnd_apply (f : stabilizerSubmonoid M x) :
    (stabilizerIsoEnd M x) f = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp 1100]
/-
**CategoryTheory.ActionCategory.stabilizerIsoEnd_symm_apply** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ActionCategory`。
形式化陈述：stabilizerIsoEnd_symm_apply (f : End _) : (stabilizerIsoEnd M x).symm f = 
f
参数：f : End _。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stabilizerIsoEnd_symm_apply (f : End _) : (stabilizerIsoEnd M x).symm f = f :=
  rfl

variable {M}

@[simp]
/-
**CategoryTheory.ActionCategory.id_val** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ActionCategory`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {X : Type u} [inst_1 : MulAction M X] (
x : CategoryTheory.ActionCategory M X),   ↑(CategoryTheory.CategoryStruct.id x) 
= 1
参数：x : CategoryTheory.ActionCategory M X；CategoryTheory.CategoryStruct.id x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem id_val (x : ActionCategory M X) : Subtype.val (𝟙 x) = 1 :=
  rfl

@[simp]
/-
**CategoryTheory.ActionCategory.comp_val** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ActionCategory`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {X : Type u} [inst_1 : MulAction M X] {
x y z : CategoryTheory.ActionCategory M X}   (f : x ⟶ y) (g : y ⟶ z), ↑(Category
Theory.CategoryStruct.comp f g) = ↑g * ↑f
参数：f : x ⟶ y；g : y ⟶ z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem comp_val {x y z : ActionCategory M X} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = g.val * f.val :=
  rfl
/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPretransitive M X] [Nonempty X] : IsConnected (ActionCategory M X) :=
  zigzag_isConnected fun x y =>
    Relation.ReflTransGen.single <|
      Or.inl <| nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)

section Group

variable {G : Type*} [Group G] [MulAction G X]

/-
**CategoryTheory.ActionCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Actio
nCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Groupoid (ActionCategory G X) :=
  CategoryTheory.groupoidOfElements _

set_option backward.isDefEq.respectTransparency.types false in
/-- Any subgroup of `G` is a vertex group in its action groupoid. -/
/-
**CategoryTheory.ActionCategory.endMulEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ActionCategory`。
形式化陈述：endMulEquivSubgroup (H : Subgroup G) : End (objEquiv G (G ⧸ H) ↑(1 : G)) ≃
* H
参数：H : Subgroup G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.stabilizer_quotient`：stabilizer_quotient {G} [Group G] (H : Su
bgroup G) : MulAction.stabilizer G ((1 : G) : G ⧸ H) = H

--- 原说明 ---
Any subgroup of `G` is a vertex group in its action groupoid.
-/
def endMulEquivSubgroup (H : Subgroup G) : End (objEquiv G (G ⧸ H) ↑(1 : G)) ≃* H :=
  MulEquiv.trans (stabilizerIsoEnd G ((1 : G) : G ⧸ H)).symm
    (MulEquiv.subgroupCongr <| stabilizer_quotient H)

/-- A target vertex `t` and a scalar `g` determine a morphism in the action groupoid. -/
/-
**CategoryTheory.ActionCategory.homOfPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ActionCategory`。
形式化陈述：homOfPair (t : X) (g : G) : @Quiver.Hom (ActionCategory G X) _ (g⁻¹ • t :)
 t
参数：t : X；g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a

--- 原说明 ---
A target vertex `t` and a scalar `g` determine a morphism in the action groupoid
.
-/
def homOfPair (t : X) (g : G) : @Quiver.Hom (ActionCategory G X) _ (g⁻¹ • t :) t :=
  Subtype.mk g (smul_inv_smul g t)

@[simp]
/-
**CategoryTheory.ActionCategory.homOfPair.val** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ActionCategory.homOfPair`。
形式化陈述：∀ {X : Type u} {G : Type u_2} [inst : Group G] [inst_1 : MulAction G X] (t
 : X) (g : G),   ↑(CategoryTheory.ActionCategory.homOfPair t g) = g
参数：t : X；g : G；CategoryTheory.ActionCategory.homOfPair t g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homOfPair.val (t : X) (g : G) : (homOfPair t g).val = g :=
  rfl

/-- Any morphism in the action groupoid is given by some pair. -/
/-
**CategoryTheory.ActionCategory.cases** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ActionCategory`。
形式化陈述：{X : Type u} →   {G : Type u_2} →     [inst : Group G] →       [inst_1 : M
ulAction G X] →         {P : ⦃a b : CategoryTheory.ActionCategory G X⦄ → (a ⟶ b)
 → Sort u_3} →           ((t : X) → (g : G) → P (CategoryTheory.ActionCategory.h
omOfPair t g)) →             ⦃a b : CategoryTheory.ActionCategory G X⦄ → (f : a 
⟶ b) → P f
参数：a ⟶ b；(t : X) → (g : G) → P (CategoryTheory.ActionCategory.homOfPair t g)。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any morphism in the action groupoid is given by some pair.
-/
protected def cases {P : ∀ ⦃a b : ActionCategory G X⦄, (a ⟶ b) → Sort*}
    (hyp : ∀ t g, P (homOfPair t g)) ⦃a b⦄ (f : a ⟶ b) : P f := by
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
/-
**CategoryTheory.ActionCategory.curry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ActionCategory`。
形式化陈述：curry (F : ActionCategory G X ⥤ SingleObj H) : G ->* (X -> H) ⋊[mulAutArro
w] G
参数：F : ActionCategory G X ⥤ SingleObj H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `G` acting on `X`, a functor from the corresponding action groupoid to a g
roup `H`
can be curried to a group homomorphism `G →* (X → H) ⋊ G`.
-/
def curry (F : ActionCategory G X ⥤ SingleObj H) : G →* (X → H) ⋊[mulAutArrow] G :=
  have F_map_eq : ∀ {a b} {f : a ⟶ b}, F.map f = (F.map (homOfPair b.back f.val) : H) := by
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
/-
**CategoryTheory.ActionCategory.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ActionCategory`。
形式化陈述：uncurry (F : G ->* (X -> H) ⋊[mulAutArrow] G) (sane : forall g, (F g).righ
t = g) : ActionCategory G X ⥤ SingleObj H where obj _
参数：F : G ->* (X -> H) ⋊[mulAutArrow] G；sane : forall g, (F g).right = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `G` acting on `X`, a group homomorphism `φ : G →* (X → H) ⋊ G` can be uncu
rried to
a functor from the action groupoid to `H`, provided that `φ g = (_, g)` for all 
`g`.
-/
def uncurry (F : G →* (X → H) ⋊[mulAutArrow] G) (sane : ∀ g, (F g).right = g) :
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

