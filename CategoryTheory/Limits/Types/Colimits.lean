/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Colimits in the category of types

We show that the category of types has all colimits, by providing the usual concrete models.

-/

@[expose] public section

universe u' v u w

namespace CategoryTheory

open Limits ConcreteCategory

variable {J : Type v} [Category.{w} J]

namespace Functor

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (F.ColimitType) :=
  small_of_surjective Quot.mk_surjective

variable (F : J ⥤ Type u)

/-- If `F : J ⥤ Type u`, then the data of a "type-theoretic" cocone of `F`
with a point in `Type u` is the same as the data of a cocone (in a categorical sense). -/
@[simps apply_pt symm_apply_pt apply_ι_app symm_apply_ι]
/-
**CategoryTheory.Functor.coconeTypesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：coconeTypesEquiv : CoconeTypes.{u} F ≃ Cocone F where toFun c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ Type u`, then the data of a "type-theoretic" cocone of `F`
with a point in `Type u` is the same as the data of a cocone (in a categorical s
ense).
-/
def coconeTypesEquiv : CoconeTypes.{u} F ≃ Cocone F where
  toFun c :=
    { pt := c.pt
      ι := { app j := ↾(c.ι j) } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

variable {F}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.CoconeTypes.isColimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.CoconeTypes`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] {F : CategoryTheo
ry.Functor J (Type u)} (c : F.CoconeTypes),   c.IsColimit ↔ Nonempty (CategoryTh
eory.Limits.IsColimit (F.coconeTypesEquiv c))
参数：Type u；c : F.CoconeTypes；CategoryTheory.Limits.IsColimit (F.coconeTypesEquiv 
c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.fac`：fac (c' : CoconeTypes.
{w₂} F) (j : J) : (hc.desc c').comp (c.ι j) = c'.ι j
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.funext`：funext {T : Type w₂
} {f g : c.pt -> T} (h : forall j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.fac_apply`：fac_apply (c' : 
CoconeTypes.{w₂} F) (j : J) (x : F.obj j) : hc.desc c' (c.ι j x) = c'.ι j x
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma CoconeTypes.isColimit_iff (c : CoconeTypes.{u} F) :
    c.IsColimit ↔ Nonempty (Limits.IsColimit (F.coconeTypesEquiv c)) := by
  constructor
  · intro hc
    exact
     ⟨{ desc s := ↾fun x => hc.desc (F.coconeTypesEquiv.symm s) x
        fac s j := by
          ext x
          exact congr_fun (hc.fac (F.coconeTypesEquiv.symm s) j) x
        uniq s m hm := by
          ext x
          exact congr_fun (hc.funext fun j ↦ funext fun y ↦ by simp [← hm j]) x }⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h ↦ ?_, fun x ↦ ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      suffices ∀ z, hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))
          (F.descColimitType c z) = f z by rw [← this x, h, ← this y]
      intro z
      obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
      exact ConcreteCategory.congr_hom (hc.fac _ j) z
    · let f₁ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun _ => ULift.up true
      let f₂ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun x => ULift.up (∃ a, F.descColimitType c a = x)
      suffices f₁ = f₂ by
        have := ConcreteCategory.congr_hom this x
        simpa [f₁, f₂] using this
      refine hc.hom_ext fun j => ?_
      ext x
      simpa [f₁, f₂] using ⟨F.ιColimitType j x, by simp⟩

end Functor

namespace Limits.Types

/-
**CategoryTheory.Limits.Types.isColimit_iff_coconeTypesIsColimit** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isColimit_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) : Nonem
pty (IsColimit c) ↔ (F.coconeTypesEquiv.symm c).IsColimit
参数：c : Cocone F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isColimit_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) :
    Nonempty (IsColimit c) ↔ (F.coconeTypesEquiv.symm c).IsColimit := by
  simp only [Functor.CoconeTypes.isColimit_iff, Equiv.apply_symm_apply]

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
/-
**CategoryTheory.Limits.Types.colimitCocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits.Types`。
形式化陈述：colimitCocone (F : J ⥤ Type u) [Small.{u} F.ColimitType] : Cocone F
参数：F : J ⥤ Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
noncomputable abbrev colimitCocone (F : J ⥤ Type u) [Small.{u} F.ColimitType] : Cocone F :=
  F.coconeTypesEquiv (F.coconeTypes.postcomp (equivShrink.{u} F.ColimitType))

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
/-
**CategoryTheory.Limits.Types.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Types`。
形式化陈述：colimitCoconeIsColimit (F : J ⥤ Type u) [Small.{u} F.ColimitType] : IsColi
mit (colimitCocone F)
参数：F : J ⥤ Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the fact that the proposed colimit cocone is the colim
it
-/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type u) [Small.{u} F.ColimitType] :
    IsColimit (colimitCocone F) :=
  Nonempty.some ((isColimit_iff_coconeTypesIsColimit _).2
    (F.isColimit_coconeTypes.of_equiv (equivShrink.{u} F.ColimitType) (by aesop)))
/-
**CategoryTheory.Limits.Types.hasColimit_iff_small_colimitType** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：hasColimit_iff_small_colimitType (F : J ⥤ Type u) : HasColimit F ↔ Small.{
u} F.ColimitType
参数：F : J ⥤ Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.bijective`：∀ {J : Type u} [
inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)
} {c : F.CoconeTypes},   c.IsColimit → Funct…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.isColimit_iff_coconeTypesIsColimit`：isColimi
t_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) : Nonempty (IsColimit
 c) ↔ (F.coconeTypesEquiv.symm c).IsColimit
-/
theorem hasColimit_iff_small_colimitType (F : J ⥤ Type u) :
    HasColimit F ↔ Small.{u} F.ColimitType :=
  ⟨fun _ ↦ small_of_injective
      ((isColimit_iff_coconeTypesIsColimit _).1 ⟨colimit.isColimit F⟩).bijective.1,
    fun _ ↦ ⟨_, colimitCoconeIsColimit F⟩⟩
/-
**CategoryTheory.Limits.Types.small_colimitType_of_hasColimit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：small_colimitType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] : Small.{u
} F.ColimitType
参数：F : J ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.hasColimit_iff_small_colimitType`：hasColimit
_iff_small_colimitType (F : J ⥤ Type u) : HasColimit F ↔ Small.{u} F.ColimitType
-/
theorem small_colimitType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] :
    Small.{u} F.ColimitType :=
  (hasColimit_iff_small_colimitType F).mp inferInstance
/-
**CategoryTheory.Limits.Types.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.Types`。
形式化陈述：hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F
参数：F : J ⥤ Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.Types.hasColimit_iff_small_colimitType`：hasColimit
_iff_small_colimitType (F : J ⥤ Type u) : HasColimit F ↔ Small.{u} F.ColimitType
· 使用定理 `CategoryTheory.Functor.instSmallColimitType`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J] (F : CategoryTheory.Functor J (Ty
pe u)),   Small.{u, max u v} F.Co…
-/
instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  (hasColimit_iff_small_colimitType F).mpr inferInstance
/-
**CategoryTheory.Limits.Types.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Types`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] [Small.{u, v} J],
   CategoryTheory.Limits.HasColimitsOfShape J (Type u)
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (Type u) where

/-- The category of types has all colimits. -/
@[stacks 002U]
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types has all colimits.
-/
instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] :
    HasColimitsOfSize.{w, v} (Type u) where

section instances

/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max w v)) :=
  inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max v w)) :=
  inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasColimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasColimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

namespace TypeMax

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
/-
**CategoryTheory.Limits.Types.TypeMax.colimitCocone** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Limits.Types.TypeMax`。
形式化陈述：colimitCocone (F : J ⥤ Type (max v u)) : Cocone F
参数：F : J ⥤ Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
abbrev colimitCocone (F : J ⥤ Type (max v u)) : Cocone F :=
  F.coconeTypesEquiv F.coconeTypes

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
/-
**CategoryTheory.Limits.Types.TypeMax.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.Types.TypeMax`。
形式化陈述：colimitCoconeIsColimit (F : J ⥤ Type (max v u)) : IsColimit (colimitCocone
 F)
参数：F : J ⥤ Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) the fact that the proposed colimit cocone is the colim
it
-/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type (max v u)) :
    IsColimit (colimitCocone F) :=
  (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

end TypeMax

variable (F : J ⥤ Type u) [HasColimit F]

attribute [local instance] small_colimitType_of_hasColimit

/-- The equivalence between the abstract colimit of `F` in `TypeCat u`
and the "concrete" definition as a quotient.
-/
/-
**CategoryTheory.Limits.Types.colimitEquivColimitType** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.Types`。
形式化陈述：colimitEquivColimitType : (colimit F : Type u) ≃ F.ColimitType
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Limits.Types.small_colimitType_of_hasColimit`：small_colim
itType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] : Small.{u} F.ColimitType
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between the abstract colimit of `F` in `TypeCat u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivColimitType : (colimit F : Type u) ≃ F.ColimitType :=
  (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]
/-
**CategoryTheory.Limits.Types.colimitEquivColimitType_symm_apply** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：colimitEquivColimitType_symm_apply (j : J) (x : F.obj j) : (colimitEquivCo
limitType F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x
参数：j : J；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.Types.small_colimitType_of_hasColimit`：small_colim
itType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] : Small.{u} F.ColimitType
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem colimitEquivColimitType_symm_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  congr_hom (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]
/-
**CategoryTheory.Limits.Types.colimitEquivColimitType_apply** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：colimitEquivColimitType_apply (j : J) (x : F.obj j) : (colimitEquivColimit
Type F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩
参数：j : J；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Limits.Types.colimitEquivColimitType_symm_apply`：colimitE
quivColimitType_symm_apply (j : J) (x : F.obj j) : (colimitEquivColimitType F).s
ymm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimitEquivColimitType_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivColimitType F).symm.injective
  simp

-- We don’t want to add `simp` to the original lemmas here.
-- `colimit.w_apply` and `colimit.ι_desc_apply` are generated (and tagged `simp`)
-- in `Mathlib/CategoryTheory/ConcreteCategory/Elementwise.lean`.
attribute [elementwise] colimit.ι_map
attribute [simp] colimit.ι_map_apply

variable {F} in
@[deprecated colimit.w_apply (since := "2026-03-06")]
/-
**CategoryTheory.Limits.Types.Colimit.w_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Types.Colimit`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.Category.{w, v} J] {F : CategoryTheo
ry.Functor J (Type u)}   [inst_1 : CategoryTheory.Limits.HasColimit F] {j j' : J
} {x : F.obj j} (f : j ⟶ j'),   (CategoryTheory.ConcreteCategory.hom (CategoryTh
eory.Limits.colimit.ι F j'))       ((CategoryTheory.ConcreteCategory.hom (F.map 
f)) x) =     (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit
.ι F j)) x
参数：Type u；f : j ⟶ j'；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.
colimit.ι F j')；(CategoryTheory.ConcreteCategory.hom (F.map f)) x；CategoryTheory
.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι F j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
-/
theorem Colimit.w_apply {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x := by
  rw [← comp_apply]
  exact congr_hom (colimit.w F f) x

@[deprecated colimit.ι_desc_apply (since := "2026-03-06")]
/-
**CategoryTheory.Limits.Types.Colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colimit.ι_desc_apply (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_hom (colimit.ι_desc s j) x

@[deprecated colimit.ι_map_apply (since := "2026-03-06")]
/-
**CategoryTheory.Limits.Types.Colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colimit.ι_map_apply {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)]
    (α : F ⟶ G) (j : J) (x : F.obj j) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_hom (colimit.ι_map α j) x

-- These were variations of the aliased lemmas with different universe variables.
-- It appears those are now strictly more powerful.
variable {F} in
/-
**CategoryTheory.Limits.Types.colimit_sound** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Types`。
形式化陈述：colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j') (w : F
.map f x = x') : colimit.ι F j x = colimit.ι F j' x'
参数：f : j ⟶ j'；w : F.map f x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.w_apply`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   (F : CategoryTheory.F…
-/
theorem colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, colimit.w_apply]

variable {F} in
/-
**CategoryTheory.Limits.Types.colimit_sound'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J} (f : j ⟶
 j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') : colimit.ι F j x = colimit.
ι F j' x'
参数：f : j ⟶ j''；f' : j' ⟶ j''；w : F.map f x = F.map f' x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.w_apply`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   (F : CategoryTheory.F…
-/
theorem colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w_apply _ f, ← colimit.w_apply _ f', w]

variable {F} in
/-
**CategoryTheory.Limits.Types.colimit_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Types`。
形式化陈述：colimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'} (w : colimit.ι F j x =
 colimit.ι F j' x') : Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩
参数：w : colimit.ι F j x = colimit.ι F j' x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.colimitEquivColimitType_apply`：colimitEquivC
olimitType_apply (j : J) (x : F.obj j) : (colimitEquivColimitType F) (colimit.ι 
F j x) = Quot.mk _ ⟨j, x⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem colimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using! congr_arg (colimitEquivColimitType F) w

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Types.jointly_surjective_of_isColimit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsCol
imit t) (x : t.pt) : exists j y, t.ι.app j y = x
参数：h : IsColimit t；x : t.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Std.Do.SPred.ext_nil`：∀ {P Q : Std.Do.SPred []}, (P.down ↔ Q.down) → P =
 Q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
    (x : t.pt) : ∃ j y, t.ι.app j y = x := by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (↾fun _ ↦ ULift.up True :
      t.pt ⟶ (ULift.{u} Prop)) ≠
    (↾fun y ↦ ULift.up (y ≠ x)))
  · refine h.hom_ext fun j ↦ ?_
    ext y
    simp only [TypeCat.Fun.toFun_apply, comp_apply, hom_ofHom,
      TypeCat.Fun.coe_mk, ne_eq, true_iff]
    exact hx j y
  · intro he
    have := ConcreteCategory.congr_hom he x
    dsimp at this
    exact of_eq_true (congrArg ULift.down this).symm rfl
/-
**CategoryTheory.Limits.Types.jointly_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Types`。
形式化陈述：jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : 
t.pt) : exists (j : J) (y : F.obj j), t.ι.app j y = x
参数：F : J ⥤ Type u；h : IsColimit t；x : t.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
-/
theorem jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ (j : J) (y : F.obj j), t.ι.app j y = x := jointly_surjective_of_isColimit h x

variable {F} in
/-- A variant of `jointly_surjective` for `x : colimit F`. -/
/-
**CategoryTheory.Limits.Types.jointly_surjective'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Types`。
形式化陈述：jointly_surjective' (x : colimit F) : exists (j : J) (y : F.obj j), colimi
t.ι F j y = x
参数：x : colimit F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective`：jointly_surjective (F : 
J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) : exists (j : J) (y : F.
obj j), t.ι.app j y = x

--- 原说明 ---
A variant of `jointly_surjective` for `x : colimit F`.
-/
theorem jointly_surjective' (x : colimit F) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x

/-- If a colimit is nonempty, also its index category is nonempty. -/
/-
**CategoryTheory.Limits.Types.nonempty_of_nonempty_colimit** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] : Nonempty (c
olimit F) -> Nonempty J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
If a colimit is nonempty, also its index category is nonempty.
-/
theorem nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] :
    Nonempty (colimit F) → Nonempty J :=
  Nonempty.map <| Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

end CategoryTheory.Limits.Types

