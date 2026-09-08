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

/-
**Fintype.IsSquare.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Fintype.IsSquare`。
形式化陈述：{α : Type u_1} → [inst : Mul α] → [Fintype α] → [DecidableEq α] → Decidabl
ePred IsSquare
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α → Prop) := fun _ => Fintype.decidableExistsFintype

/-- The cardinality of `Fin 2` is even, `Fact` version.
This `Fact` is needed as an instance by `Matrix.SpecialLinearGroup.instNeg`. -/
/-
**Fintype.card_fin_two** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：card_fin_two : Fact (Even (Fintype.card (Fin 2)))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of `Fin 2` is even, `Fact` version.
This `Fact` is needed as an instance by `Matrix.SpecialLinearGroup.instNeg`.
-/
instance card_fin_two : Fact (Even (Fintype.card (Fin 2))) :=
  ⟨⟨1, rfl⟩⟩

end Fintype

