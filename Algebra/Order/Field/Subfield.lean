/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# Ordered instances on subfields
-/

public section

namespace Subfield
variable {K : Type*}

/-- A subfield of an ordered field is an ordered field. -/
/-
**Subfield.toIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：toIsStrictOrderedRing [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s
 : Subfield K) : IsStrictOrderedRing s
参数：s : Subfield K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isStrictOrderedRing`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : PartialOrder R] [IsStrictOrderedRing R]   [inst_3 
: Semiring S] [inst_4 : Part…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subfield of an ordered field is an ordered field.
-/
instance toIsStrictOrderedRing [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K) :
    IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end Subfield

