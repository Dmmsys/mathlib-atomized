/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Limits in the category of types.

We show that the category of types has all limits, by providing the usual concrete models.

-/

@[expose] public section

universe u' v u w

namespace CategoryTheory.Limits.Types

open ConcreteCategory

section limit_characterization

variable {J : Type v} [Category.{w} J] {F : J ⥤ Type u}

/-- Given a section of a functor F into `Type*`,
  construct a cone over F with `PUnit` as the cone point. -/
/-
**CategoryTheory.Limits.Types.coneOfSection** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Types`。
形式化陈述：coneOfSection {s} (hs : s in F.sections) : Cone F where pt
参数：hs : s in F.sections。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a section of a functor F into `Type*`,
  construct a cone over F with `PUnit` as the cone point.
-/
def coneOfSection {s} (hs : s ∈ F.sections) : Cone F where
  pt := PUnit
  π := { app j := ↾fun _ ↦ s j, naturality _ _ f := by ext; exact (hs f).symm }

/-- Given a cone over a functor F into `Type*` and an element in the cone point,
  construct a section of F. -/
/-
**CategoryTheory.Limits.Types.sectionOfCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Types`。
形式化陈述：sectionOfCone (c : Cone F) (x : c.pt) : F.sections
参数：c : Cone F；x : c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone over a functor F into `Type*` and an element in the cone point,
  construct a section of F.
-/
def sectionOfCone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j ↦ c.π.app j x, fun f ↦ congr_hom (c.π.naturality f).symm x⟩
/-
**CategoryTheory.Limits.Types.isLimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Types`。
形式化陈述：isLimit_iff (c : Cone F) : Nonempty (IsLimit c) ↔ forall s in F.sections, 
exists! x : c.pt, forall j, c.π.app j x = s j
参数：c : Cone F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ ∀ s ∈ F.sections, ∃! x : c.pt, ∀ j, c.π.app j x = s j := by
  refine ⟨fun ⟨t⟩ s hs ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j ↦ congr_hom (t.fac cs j) ⟨⟩,
      fun x hx ↦ congr_hom (CC := fun X ↦ X)
        (t.uniq cs (↾fun _ ↦ x) fun j ↦ by ext; exact hx j) ⟨⟩⟩
  · have := fun c y ↦ h _ (sectionOfCone c y).2
    choose x hx using fun c y ↦ h _ (sectionOfCone c y).2
    exact ⟨fun d ↦ ↾(x d), fun c j ↦ by ext y; exact (hx c y).1 j,
      fun c f hf ↦ by ext y; exact (hx c y).2 (f y) (fun j ↦ congr_hom (hf j) y)⟩
/-
**CategoryTheory.Limits.Types.isLimit_iff_bijective_sectionOfCone** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isLimit_iff_bijective_sectionOfCone (c : Cone F) : Nonempty (IsLimit c) ↔ 
(Types.sectionOfCone c).Bijective
参数：c : Cone F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.sections_ext_iff`：sections_ext_iff {F : J ⥤ Type 
w} {x y : F.sections} : x = y ↔ forall j, x.val j = y.val j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLimit_iff_bijective_sectionOfCone (c : Cone F) :
    Nonempty (IsLimit c) ↔ (Types.sectionOfCone c).Bijective := by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

/-- The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
  sections of `F`. -/
/-
**CategoryTheory.Limits.Types.isLimitEquivSections** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Types`。
形式化陈述：isLimitEquivSections {c : Cone F} (t : IsLimit c) : c.pt ≃ F.sections wher
e toFun
参数：t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between a limiting cone of `F` in `Type u` and the "concrete" de
finition as the
  sections of `F`.
-/
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_hom (t.uniq (coneOfSection _)
    (↾fun _ ↦ x) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_hom (t.fac (coneOfSection s.2) j) ⟨⟩)

@[simp]
/-
**CategoryTheory.Limits.Types.isLimitEquivSections_apply** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.Types`。
形式化陈述：isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J) (x : c.pt)
 : (isLimitEquivSections t x : forall j, F.obj j) j = c.π.app j x
参数：t : IsLimit c；j : J；x : c.pt。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J)
    (x : c.pt) : (isLimitEquivSections t x : ∀ j, F.obj j) j = c.π.app j x := rfl

@[simp]
/-
**CategoryTheory.Limits.Types.isLimitEquivSections_symm_apply** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c) (x : F.sectio
ns) (j : J) : dsimp% c.π.app j ((isLimitEquivSections t).symm x) = (x : forall j
, F.obj j) j
参数：t : IsLimit c；x : F.sections；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c)
    (x : F.sections) (j : J) :
    dsimp% c.π.app j ((isLimitEquivSections t).symm x) = (x : ∀ j, F.obj j) j := by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl

end limit_characterization

variable {J : Type v} [Category.{w} J]

/-! We now provide two distinct implementations in the category of types.

The first, in the `CategoryTheory.Limits.Types.Small` namespace,
assumes `Small.{u} J` and constructs `J`-indexed limits in `Type u`.

The second, in the `CategoryTheory.Limits.Types.TypeMax` namespace
constructs limits for functors `F : J ⥤ Type (max v u)`, for `J : Type v`.
This construction is slightly nicer, as the limit is definitionally just `F.sections`,
rather than `Shrink F.sections`, which makes an arbitrary choice of `u`-small representative.

Hopefully we might be able to entirely remove the `TypeMax` constructions,
but for now they are useful glue for the later parts of the library.
-/

namespace Small

variable (F : J ⥤ Type u)

section

variable [Small.{u} F.sections]

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
/-
**CategoryTheory.Limits.Types.Small.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Types.Small`。
形式化陈述：limitCone : Cone F where pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
(internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
noncomputable def limitCone : Cone F where
  pt := Shrink F.sections
  π :=
    { app j := ↾fun u => ((equivShrink F.sections).symm u).val j }

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/-
**CategoryTheory.Limits.Types.Small.limitCone_pt_ext** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.Types.Small`。
形式化陈述：limitCone_pt_ext {x y : (limitCone F).pt} (w : (equivShrink F.sections).sy
mm x = (equivShrink F.sections).symm y) : x = y
参数：limitCone F；w : (equivShrink F.sections).symm x = (equivShrink F.sections).sy
mm y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma limitCone_pt_ext {x y : (limitCone F).pt}
    (w : (equivShrink F.sections).symm x = (equivShrink F.sections).symm y) : x = y := by
  simp_all

set_option backward.defeqAttrib.useBackward true in
/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
/-
**CategoryTheory.Limits.Types.Small.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Types.Small`。
形式化陈述：limitConeIsLimit : IsLimit (limitCone.{v, u} F) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the fact that the proposed limit cone is the limit
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) where
  lift s := ↾fun v ↦ equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using! congr_hom (w j) x

end

end Small

/-
**CategoryTheory.Limits.Types.hasLimit_iff_small_sections** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Types`。
形式化陈述：hasLimit_iff_small_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.se
ctions
参数：F : J ⥤ Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.isLimit_iff_bijective_sectionOfCone`：isLimit
_iff_bijective_sectionOfCone (c : Cone F) : Nonempty (IsLimit c) ↔ (Types.sectio
nOfCone c).Bijective
-/
theorem hasLimit_iff_small_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections :=
  ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩

-- TODO: If `UnivLE` works out well, we will eventually want to deprecate these
-- definitions, and probably as a first step put them in namespace or otherwise rename them.
section TypeMax

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
/-
**CategoryTheory.Limits.Types.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Types`。
形式化陈述：limitCone (F : J ⥤ Type (max v u)) : Cone F where pt
参数：F : J ⥤ Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
noncomputable def limitCone (F : J ⥤ Type (max v u)) : Cone F where
  pt := F.sections
  π := { app j := ↾fun u => u.val j }

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
/-
**CategoryTheory.Limits.Types.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Types`。
形式化陈述：limitConeIsLimit (F : J ⥤ Type (max v u)) : IsLimit (limitCone F) where li
ft s
参数：F : J ⥤ Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the fact that the proposed limit cone is the limit
-/
noncomputable def limitConeIsLimit (F : J ⥤ Type (max v u)) : IsLimit (limitCone F) where
  lift s := ↾fun v ↦
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x
    apply Subtype.ext
    funext j
    exact congr_hom (w j) x

end TypeMax


/-!
The results in this section have a `UnivLE.{v, u}` hypothesis,
but as they only use the constructions from the `CategoryTheory.Limits.Types.UnivLE` namespace
in their definitions (rather than their statements),
we leave them in the main `CategoryTheory.Limits.Types` namespace.
-/
section UnivLE

open UnivLE

/-
**CategoryTheory.Limits.Types.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.Types`。
形式化陈述：hasLimit [Small.{u} J] (F : J ⥤ Type u) : HasLimit F
参数：F : J ⥤ Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.Types.hasLimit_iff_small_sections`：hasLimit_iff_sm
all_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasLimit [Small.{u} J] (F : J ⥤ Type u) : HasLimit F :=
  (hasLimit_iff_small_sections F).mpr inferInstance
/-
**CategoryTheory.Limits.Types.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.Types`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] [Small.{u, v} J],
   CategoryTheory.Limits.HasLimitsOfShape J (Type u)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (Type u) where

/--
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small limits. -/
@[stacks 002U]
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small
 limits.
-/
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] :
    HasLimitsOfSize.{w, v} (Type u) where
  has_limits_of_shape _ := { }

variable (F : J ⥤ Type u) [HasLimit F]

/-- The equivalence between the abstract limit of `F` in `Type max v u`
and the "concrete" definition as the sections of `F`.
-/
/-
**CategoryTheory.Limits.Types.limitEquivSections** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Types`。
形式化陈述：limitEquivSections : limit F ≃ F.sections
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the abstract limit of `F` in `Type max v u`
and the "concrete" definition as the sections of `F`.
-/
noncomputable def limitEquivSections : limit F ≃ F.sections :=
  isLimitEquivSections (limit.isLimit F)

@[simp]
/-
**CategoryTheory.Limits.Types.limitEquivSections_apply** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.Types`。
形式化陈述：limitEquivSections_apply (x : limit F) (j : J) : dsimp% ((limitEquivSectio
ns F) x : forall j, F.obj j) j = limit.π F j x
参数：x : limit F；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitEquivSections_apply (x : limit F) (j : J) :
    dsimp% ((limitEquivSections F) x : ∀ j, F.obj j) j = limit.π F j x :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Types.limitEquivSections_symm_apply** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：limitEquivSections_symm_apply (x : F.sections) (j : J) : limit.π F j ((lim
itEquivSections F).symm x) = (x : forall j, F.obj j) j
参数：x : F.sections；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.isLimitEquivSections_symm_apply`：isLimitEqui
vSections_symm_apply {c : Cone F} (t : IsLimit c) (x : F.sections) (j : J) : dsi
mp% c.π.app j ((isLimitEquivSections t).symm x) =…
-/
theorem limitEquivSections_symm_apply (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : ∀ j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _

/-- The limit of a functor `F : J ⥤ Type _` is naturally isomorphic to `F.sections`. -/
/-
**CategoryTheory.Limits.Types.limNatIsoSectionsFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Types`。
形式化陈述：limNatIsoSectionsFunctor : (lim : (J ⥤ Type (max u v)) ⥤ Type (max u v)) ≅
 Functor.sectionsFunctor J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of a functor `F : J ⥤ Type _` is naturally isomorphic to `F.sections`.
-/
noncomputable def limNatIsoSectionsFunctor :
    (lim : (J ⥤ Type (max u v)) ⥤ Type (max u v)) ≅ Functor.sectionsFunctor J :=
  NatIso.ofComponents (fun F ↦ (limitEquivSections F).toIso)
    fun f ↦ by ext x; exact Subtype.ext (funext fun j ↦ congr_hom (limMap_π f j) x)

/-- Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
/-
**CategoryTheory.Limits.Types.Limit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Types.Limit`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.Category.{w, v} J] →     (F : Cate
goryTheory.Functor J (Type u)) →       [inst_1 : CategoryTheory.Limits.HasLimit 
F] →         (x : (j : J) → F.obj j) →           (∀ (j j' : J) (f : j ⟶ j'), (Ca
tegoryTheory.ConcreteCategory.hom (F.map f)) (x j) = x j') →             Categor
yTheory.Limits.limit F
参数：F : CategoryTheory.Functor J (Type u)；x : (j : J) → F.obj j；∀ (j j' : J) (f :
 j ⟶ j'), (CategoryTheory.ConcreteCategory.hom (F.map f)) (x j) = x j'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
noncomputable def Limit.mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') :
    limit F :=
  (limitEquivSections F).symm ⟨x, h _ _⟩

@[simp]
/-
**CategoryTheory.Limits.Types.Limit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Limit.π_mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  simp

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
/-
**CategoryTheory.Limits.Types.limit_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Types`。
形式化陈述：limit_ext (x y : limit F) (w : forall j, limit.π F j x = limit.π F j y) : 
x = y
参数：x y : limit F；w : forall j, limit.π F j x = limit.π F j y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit_ext (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
    x = y := by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]

@[ext]
/-
**CategoryTheory.Limits.Types.limit_ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Types`。
形式化陈述：limit_ext' (F' : J ⥤ Type v) (x y : limit F') (w : forall j, limit.π F' j 
x = limit.π F' j y) : x = y
参数：F' : J ⥤ Type v；x y : limit F'；w : forall j, limit.π F' j x = limit.π F' j y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
-/
theorem limit_ext' (F' : J ⥤ Type v) (x y : limit F')
    (w : ∀ j, limit.π F' j x = limit.π F' j y) : x = y :=
  limit_ext F' x y w
/-
**CategoryTheory.Limits.Types.limit_ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：limit_ext_iff' (F' : J ⥤ Type v) (x y : limit F') : x = y ↔ forall j, limi
t.π F' j x = limit.π F' j y
参数：F' : J ⥤ Type v；x y : limit F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.limit_ext'`：limit_ext' (F' : J ⥤ Type v) (x 
y : limit F') (w : forall j, limit.π F' j x = limit.π F' j y) : x = y
-/
theorem limit_ext_iff' (F' : J ⥤ Type v) (x y : limit F') :
    x = y ↔ ∀ j, limit.π F' j x = limit.π F' j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩

-- `limit.lift_π_apply` and `limit.w_apply` are generated (and tagged `simp`)
-- in `Mathlib/CategoryTheory/ConcreteCategory/Elementwise.lean`.
attribute [elementwise] limMap_π
attribute [simp] limMap_π_apply

variable {F} in
@[deprecated limit.w_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.w_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Types.Limit`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] {F : CategoryTheo
ry.Functor J (Type u)}   [inst_1 : CategoryTheory.Limits.HasLimit F] {j j' : J} 
{x : CategoryTheory.Limits.limit F} (f : j ⟶ j'),   (CategoryTheory.ConcreteCate
gory.hom (F.map f))       ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.
Limits.limit.π F j)) x) =     (CategoryTheory.ConcreteCategory.hom (CategoryTheo
ry.Limits.limit.π F j')) x
参数：Type u；f : j ⟶ j'；CategoryTheory.ConcreteCategory.hom (F.map f)；(CategoryTheo
ry.ConcreteCategory.hom (CategoryTheory.Limits.limit.π F j)) x；CategoryTheory.Co
ncreteCategory.hom (CategoryTheory.Limits.limit.π F j')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.w_apply`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   (F : CategoryTheory.F…
-/
theorem Limit.w_apply {j j' : J} {x : (limit F : Type u)} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Limit.lift_π_apply (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Limit.map_π_apply {F G : J ⥤ Type u} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
    (x : limit F) : limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  limMap_π_apply _ _ _

@[deprecated limit.w_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.w_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types.Limit`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] {F' : CategoryThe
ory.Functor J (Type v)} {j j' : J}   {x : CategoryTheory.Limits.limit F'} (f : j
 ⟶ j'),   (CategoryTheory.ConcreteCategory.hom (F'.map f))       ((CategoryTheor
y.ConcreteCategory.hom (CategoryTheory.Limits.limit.π F' j)) x) =     (CategoryT
heory.ConcreteCategory.hom (CategoryTheory.Limits.limit.π F' j')) x
参数：Type v；f : j ⟶ j'；CategoryTheory.ConcreteCategory.hom (F'.map f)；(CategoryThe
ory.ConcreteCategory.hom (CategoryTheory.Limits.limit.π F' j)) x；CategoryTheory.
ConcreteCategory.hom (CategoryTheory.Limits.limit.π F' j')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.limit.w_apply`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   (F : CategoryTheory.F…
-/
theorem Limit.w_apply' {F' : J ⥤ Type v} {j j' : J} {x : (limit F' : Type v)}
    (f : j ⟶ j') : F'.map f (limit.π F' j x) = limit.π F' j' x :=
  limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Limit.lift_π_apply' (F' : J ⥤ Type v) (s : Cone F') (j : J) (x : s.pt) :
    limit.π F' j (limit.lift F' s x) = s.π.app j x :=
  limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]
/-
**CategoryTheory.Limits.Types.Limit.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Limit.map_π_apply' {F' G' : J ⥤ Type v} (α : F' ⟶ G') (j : J)
    (x : (limit F' : Type v)) : limit.π G' j (limMap α x) = α.app j (limit.π F' j x) :=
  limMap_π_apply _ _ _

end UnivLE

/-!
In this section we verify that instances are available as expected.
-/
section instances

/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max w v)) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max v w)) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasLimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasLimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [UnivLE.{v, u}] : HasLimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

end CategoryTheory.Limits.Types

