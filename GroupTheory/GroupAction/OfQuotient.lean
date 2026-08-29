/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# MulAction and MulDistribMulAction of quotient group on fixed points

Given a `MulAction`/`MulDistribMulAction` of a group `G` on `A` and a normal subgroup `H` of `G`,
there is a `MulAction`/`MulDistribMulAction` of the quotient group `G ⧸ H` on `fixedPoints H A`.

-/

public section

namespace MulAction

variable {G : Type*} [Group G] {A : Type*} [MulAction G A]

variable {H : Subgroup G} [H.Normal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (G ⧸ H) (fixedPoints H A)
  body: ofEndHom
    QuotientGroup.lift H (toEndHom : G ->* Function.End (fixedPoints H A))
    (fun g hg => by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]

中文:
实例 :
  签名: MulAction (G ⧸ H) (fixedPoints H A)
  定义体: ofEndHom
    QuotientGroup.lift H (toEndHom : G ->* Function.End (fixedPoints H A))
    (fun g hg => by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]

Depends on / 依赖: Function, Function.End, QuotientGroup, QuotientGroup.lift, fixedPoints, ofEndHom, toEndHom
-/
instance : MulAction (G ⧸ H) (fixedPoints H A) :=
ofEndHom
    QuotientGroup.lift H (toEndHom : G ->* Function.End (fixedPoints H A))
    (fun g hg => by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]
/--
lemma `coe_quotient_smul_fixedPoints` / 引理 `coe_quotient_smul_fixedPoints`

English:
lemma coe_quotient_smul_fixedPoints
  given: (g : G) (a : fixedPoints H A)
  proof: rfl

@[simp]

中文:
引理 coe_quotient_smul_fixedPoints
  条件: (g : G) (a : fixedPoints H A)
  证明: rfl

@[simp]
-/
lemma coe_quotient_smul_fixedPoints (g : G) (a : fixedPoints H A) :
    (g : G ⧸ H) • a = g • a := rfl

@[simp]
/--
lemma `quotient_out_smul_fixedPoints` / 引理 `quotient_out_smul_fixedPoints`

English:
lemma quotient_out_smul_fixedPoints
  given: (g : G ⧸ H) (a : fixedPoints H A)
  proof: by
  conv_rhs => rw [← g.out_eq]
  rfl

中文:
引理 quotient_out_smul_fixedPoints
  条件: (g : G ⧸ H) (a : fixedPoints H A)
  证明: by
  conv_rhs => rw [← g.out_eq]
  rfl

Depends on / 依赖: conv_rhs, g.out_eq, out_eq
-/
lemma quotient_out_smul_fixedPoints (g : G ⧸ H) (a : fixedPoints H A) :
    g.out • a = g • a := by
  conv_rhs => rw [← g.out_eq]
  rfl

end MulAction

namespace MulDistribMulAction

open MulAction

variable {G : Type*} [Group G] {A : Type*} [Monoid A] [MulDistribMulAction G A]

variable {H : Subgroup G} [H.Normal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H A)
  body: (inferInstance : MulAction (G ⧸ H) (fixedPoints H A))
  smul_mul g a b := g.induction_on fun g => Subtype.ext (smul_mul g a.1 b.1)
  smul_one g := g.induction_on fun g => Subtype.ext (smul_one g)

中文:
实例 :
  签名: MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H A)
  定义体: (inferInstance : MulAction (G ⧸ H) (fixedPoints H A))
  smul_mul g a b := g.induction_on fun g => Subtype.ext (smul_mul g a.1 b.1)
  smul_one g := g.induction_on fun g => Subtype.ext (smul_one g)

Depends on / 依赖: MulAction, fixedPoints
-/
instance : MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H A) where
  __ := (inferInstance : MulAction (G ⧸ H) (fixedPoints H A))
  smul_mul g a b := g.induction_on fun g => Subtype.ext (smul_mul g a.1 b.1)
  smul_one g := g.induction_on fun g => Subtype.ext (smul_one g)

open scoped FixedPoints

variable {α : Type*} [Group α] [MulDistribMulAction G α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α)
  body: inferInstanceAs MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)

中文:
实例 :
  签名: MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α)
  定义体: inferInstanceAs MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)

Depends on / 依赖: FixedPoints, FixedPoints.submonoid, MulDistribMulAction, submonoid
-/
instance : MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α) :=
inferInstanceAs MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)

end MulDistribMulAction
