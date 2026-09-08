/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.DiscreteQuotient

/-!
# Profinite sets as limits of finite sets.

We show that any profinite set is isomorphic to the limit of its
discrete (hence finite) quotients.

## Definitions

There are a handful of definitions in this file, given `X : Profinite`:
1. `X.fintypeDiagram` is the functor `DiscreteQuotient X ⥤ FintypeCat` whose limit
  is isomorphic to `X` (the limit taking place in `Profinite` via `FintypeCat.toProfinite`, see 2).
2. `X.diagram` is an abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`.
3. `X.asLimitCone` is the cone over `X.diagram` whose cone point is `X`.
4. `X.isoAsLimitConeLift` is the isomorphism `X ≅ (Profinite.limitCone X.diagram).X` induced
  by lifting `X.asLimitCone`.
5. `X.asLimitConeIso` is the isomorphism `X.asLimitCone ≅ (Profinite.limitCone X.diagram)`
  induced by `X.isoAsLimitConeLift`.
6. `X.asLimit` is a term of type `IsLimit X.asLimitCone`.
7. `X.lim : CategoryTheory.Limits.LimitCone X.asLimitCone` is a bundled combination of 3 and 6.

-/

@[expose] public section


noncomputable section

open CategoryTheory

namespace Profinite

universe u

variable (X : Profinite.{u})

/-- The functor `DiscreteQuotient X ⥤ Fintype` whose limit is isomorphic to `X`. -/
/-
**Profinite.fintypeDiagram** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `DiscreteQuotient X ⥤ Fintype` whose limit is isomorphic to `X`.
-/
def fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where
  obj S := FintypeCat.of S
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)

/-- An abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
/-
**Profinite.diagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `Profinite`。
形式化陈述：diagram : DiscreteQuotient X ⥤ Profinite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`.
-/
abbrev diagram : DiscreteQuotient X ⥤ Profinite :=
  X.fintypeDiagram ⋙ FintypeCat.toProfinite

/-- A cone over `X.diagram` whose cone point is `X`. -/
/-
**Profinite.asLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：asLimitCone : CategoryTheory.Limits.Cone X.diagram
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `X.diagram` whose cone point is `X`.
-/
def asLimitCone : CategoryTheory.Limits.Cone X.diagram :=
  { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.isIso_asLimitCone_lift** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：isIso_asLimitCone_lift : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X
.asLimitCone)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.isIso_of_bijective`：isIso_of_bijective {X Y : CompHausLike.
{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) : IsIso f
· 使用定理 `DiscreteQuotient.eq_of_forall_proj_eq`：eq_of_forall_proj_eq [T2Space X] 
[CompactSpace X] [disc : TotallyDisconnectedSpace X] {x y : X} (h : forall Q : D
iscreteQuotient X, Q.proj x…
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteQuotient.exists_of_compat`：exists_of_compat [CompactSpace X] (Qs
 : (Q : DiscreteQuotient X) -> Q) (compat : forall (A B : DiscreteQuotient X) (h
 : A <= B), ofLE h (Qs …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
instance isIso_asLimitCone_lift : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone) :=
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists_of_compat (fun S => a.val S) fun _ _ h => a.prop (homOfLE h)
        use b
        -- ext S : 3 -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` does not work, replaced with following
        -- three lines.
        apply Subtype.ext
        apply funext
        rintro S
        -- Porting note: end replacement block
        apply hb)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `X` and the explicit limit of `X.diagram`,
induced by lifting `X.asLimitCone`.
-/
/-
**Profinite.isoAsLimitConeLift** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `X` and the explicit limit of `X.diagram`,
induced by lifting `X.asLimitCone`.
-/
def isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt :=
  asIso <| (limitConeIsLimit.{u, u} _).lift X.asLimitCone

/-- The isomorphism of cones `X.asLimitCone` and `Profinite.limitCone X.diagram`.
The underlying isomorphism is defeq to `X.isoAsLimitConeLift`.
-/
/-
**Profinite.asLimitConeIso** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of cones `X.asLimitCone` and `Profinite.limitCone X.diagram`.
The underlying isomorphism is defeq to `X.isoAsLimitConeLift`.
-/
def asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _ :=
  Limits.Cone.ext (isoAsLimitConeLift _) fun _ => rfl

/-- `X.asLimitCone` is indeed a limit cone. -/
/-
**Profinite.asLimit** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.asLimitCone` is indeed a limit cone.
-/
def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

/-- A bundled version of `X.asLimitCone` and `X.asLimit`. -/
/-
**Profinite.lim** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：lim : Limits.LimitCone X.diagram
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled version of `X.asLimitCone` and `X.asLimit`.
-/
def lim : Limits.LimitCone X.diagram :=
  ⟨X.asLimitCone, X.asLimit⟩

end Profinite

