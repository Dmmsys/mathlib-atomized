/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Even

/-!
# The cardinality of `Fin 2` is even.
-/

public section


variable {α : Type*}

namespace Fintype

/--
Instance `IsSquare.decidablePred` / 实例 `IsSquare.decidablePred`

English:
instance IsSquare.decidablePred
  signature: [Mul α] [Fintype α] [DecidableEq α]
  body: fun _ => Fintype.decidableExistsFintype

中文:
实例 IsSquare.decidablePred
  签名: [乘法 α] [有限类型 α] [DecidableEq α]
  定义体: fun _ => Fintype.decidableExistsFintype

Depends on / 依赖: Fintype, Fintype.decidableExistsFintype, decidableExistsFintype
-/
instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α -> Prop) := fun _ => Fintype.decidableExistsFintype

/--
Instance `card_fin_two` / 实例 `card_fin_two`

English:
instance card_fin_two
  signature: : Fact (Even (Fintype.card (Fin 2)))
  body: ⟨⟨1, rfl⟩⟩

中文:
实例 card_fin_two
  签名: : Fact (Even (有限类型.card (有限集 2)))
  定义体: ⟨⟨1, rfl⟩⟩
-/
instance card_fin_two : Fact (Even (Fintype.card (Fin 2))) :=
  ⟨⟨1, rfl⟩⟩

end Fintype
