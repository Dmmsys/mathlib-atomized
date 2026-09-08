/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurable space instance for additive characters

This file endows `AddChar A M` with the discrete measurable space structure whenever `A` is a finite
discrete measurable space.

## TODO

Give the definition in the correct generality.
-/

public section

namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M] [MeasurableSpace A] [MeasurableSpace M]

@[nolint unusedArguments]
/-
**AddChar.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] : MeasurableSpa
ce (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    MeasurableSpace (AddChar A M) :=
  ⊤
/-
**AddChar.instDiscreteMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instDiscreteMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] : Discr
eteMeasurableSpace (AddChar A M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    DiscreteMeasurableSpace (AddChar A M) :=
  ⟨fun _ ↦ trivial⟩

end AddChar

