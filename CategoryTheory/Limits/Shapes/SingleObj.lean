/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# (Co)limits of functors out of `SingleObj M`

We characterise (co)limits of shape `SingleObj M`. Currently only in the category of types.

## Main results

* `SingleObj.Types.limitEquivFixedPoints`: The limit of `J : SingleObj G ⥤ Type u` is the fixed
  points of `J.obj (SingleObj.star G)` under the induced action.

* `SingleObj.Types.colimitEquivQuotient`: The colimit of `J : SingleObj G ⥤ Type u` is the
  quotient of `J.obj (SingleObj.star G)` by the induced action.

-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v

namespace CategoryTheory

namespace Limits

namespace SingleObj

variable {M G : Type v} [Monoid M] [Group G]

/-- The induced `G`-action on the target of `J : SingleObj G ⥤ Type u`. -/
/-
**CategoryTheory.Limits.SingleObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its.SingleObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced `G`-action on the target of `J : SingleObj G ⥤ Type u`.
-/
instance (J : SingleObj M ⥤ Type u) : MulAction M (J.obj (SingleObj.star M)) where
  smul g x := J.map g x
  one_smul x := by
    change J.map (𝟙 _) x = x
    simp
  mul_smul g h x := by
    change J.map (g * h) x = (J.map h ≫ J.map g) x
    rw [← SingleObj.comp_as_mul]
    · simp
      rfl

section Limits

variable (J : SingleObj M ⥤ Type u)

/-- The equivalence between sections of `J : SingleObj M ⥤ Type u` and fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps]
/-
**CategoryTheory.Limits.SingleObj.Types.sections.equivFixedPoints** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.SingleObj.Types.sections`。
形式化陈述：{M : Type v} →   [inst : Monoid M] →     (J : CategoryTheory.Functor (Cate
goryTheory.SingleObj M) (Type u)) →       ↑J.sections ≃ ↑(MulAction.fixedPoints 
M (J.obj (CategoryTheory.SingleObj.star M)))
参数：J : CategoryTheory.Functor (CategoryTheory.SingleObj M) (Type u)；MulAction.fi
xedPoints M (J.obj (CategoryTheory.SingleObj.star M))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between sections of `J : SingleObj M ⥤ Type u` and fixed points 
of the
induced action on `J.obj (SingleObj.star M)`.
-/
def Types.sections.equivFixedPoints :
    J.sections ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) where
  toFun s := ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ ↦ p.val, p.property⟩

/-- The limit of `J : SingleObj M ⥤ Type u` is equivalent to the fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps!]
/-
**CategoryTheory.Limits.SingleObj.Types.limitEquivFixedPoints** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.SingleObj.Types`。
形式化陈述：{M : Type v} →   [inst : Monoid M] →     (J : CategoryTheory.Functor (Cate
goryTheory.SingleObj M) (Type u)) →       CategoryTheory.Limits.limit J ≃ ↑(MulA
ction.fixedPoints M (J.obj (CategoryTheory.SingleObj.star M)))
参数：J : CategoryTheory.Functor (CategoryTheory.SingleObj M) (Type u)；MulAction.fi
xedPoints M (J.obj (CategoryTheory.SingleObj.star M))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The limit of `J : SingleObj M ⥤ Type u` is equivalent to the fixed points of the
induced action on `J.obj (SingleObj.star M)`.
-/
noncomputable def Types.limitEquivFixedPoints :
    limit J ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) :=
  (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

end Limits

section Colimits

variable {G : Type v} [Group G] (J : SingleObj G ⥤ Type u)

/-- The relation used to construct colimits in types for `J : SingleObj G ⥤ Type u` is
equivalent to the `MulAction.orbitRel` equivalence relation on `J.obj (SingleObj.star G)`. -/
/-
**CategoryTheory.Limits.SingleObj.colimitTypeRel_iff_orbitRel** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits.SingleObj`。
形式化陈述：colimitTypeRel_iff_orbitRel (x y : J.obj (SingleObj.star G)) : J.ColimitTy
peRel ⟨SingleObj.star G, x⟩ ⟨SingleObj.star G, y⟩ ↔ MulAction.orbitRel G (J.obj 
(SingleObj.star G)) x y
参数：x y : J.obj (SingleObj.star G)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x

--- 原说明 ---
The relation used to construct colimits in types for `J : SingleObj G ⥤ Type u` 
is
equivalent to the `MulAction.orbitRel` equivalence relation on `J.obj (SingleObj
.star G)`.
-/
lemma colimitTypeRel_iff_orbitRel (x y : J.obj (SingleObj.star G)) :
    J.ColimitTypeRel ⟨SingleObj.star G, x⟩ ⟨SingleObj.star G, y⟩ ↔
      MulAction.orbitRel G (J.obj (SingleObj.star G)) x y := by
  conv => rhs; rw [Setoid.comm']
  change (∃ g : G, y = g • x) ↔ (∃ g : G, g • x = y)
  grind

/-- The explicit quotient construction of the colimit of `J : SingleObj G ⥤ Type u` is
equivalent to the quotient of `J.obj (SingleObj.star G)` by the induced action. -/
@[simps]
/-
**CategoryTheory.Limits.SingleObj.colimitTypeRelEquivOrbitRelQuotient** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Limits.SingleObj`。
形式化陈述：colimitTypeRelEquivOrbitRelQuotient : J.ColimitType ≃ MulAction.orbitRel.Q
uotient G (J.obj (SingleObj.star G)) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit quotient construction of the colimit of `J : SingleObj G ⥤ Type u` 
is
equivalent to the quotient of `J.obj (SingleObj.star G)` by the induced action.
-/
def colimitTypeRelEquivOrbitRelQuotient :
    J.ColimitType ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) where
  toFun := Quot.lift (fun p => ⟦p.2⟧) <| fun a b h => Quotient.sound <|
    (colimitTypeRel_iff_orbitRel J a.2 b.2).mp h
  invFun := Quot.lift (fun x => Quot.mk _ ⟨SingleObj.star G, x⟩) <| fun a b h =>
    Quot.sound <| (colimitTypeRel_iff_orbitRel J a b).mpr h
  left_inv := fun x => Quot.inductionOn x (fun _ ↦ rfl)
  right_inv := fun x => Quot.inductionOn x (fun _ ↦ rfl)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit of `J : SingleObj G ⥤ Type u` is equivalent to the quotient of
`J.obj (SingleObj.star G)` by the induced action. -/
@[simps!]
/-
**CategoryTheory.Limits.SingleObj.Types.colimitEquivQuotient** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.SingleObj.Types`。
形式化陈述：{G : Type v} →   [inst : Group G] →     (J : CategoryTheory.Functor (Categ
oryTheory.SingleObj G) (Type u)) →       CategoryTheory.Limits.colimit J ≃ MulAc
tion.orbitRel.Quotient G (J.obj (CategoryTheory.SingleObj.star G))
参数：J : CategoryTheory.Functor (CategoryTheory.SingleObj G) (Type u)；J.obj (Categ
oryTheory.SingleObj.star G)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The colimit of `J : SingleObj G ⥤ Type u` is equivalent to the quotient of
`J.obj (SingleObj.star G)` by the induced action.
-/
noncomputable def Types.colimitEquivQuotient :
    colimit J ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) :=
  (Types.colimitEquivColimitType J).trans (colimitTypeRelEquivOrbitRelQuotient J)

end Colimits

end SingleObj

end Limits

end CategoryTheory

