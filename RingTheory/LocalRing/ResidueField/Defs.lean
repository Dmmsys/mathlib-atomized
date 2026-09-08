/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!

# Residue Field of local rings

## Main definitions

* `IsLocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.
* `IsLocalRing.residue`: The quotient map from a local ring to its residue field.
-/

@[expose] public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
@[wikidata Q7315530]
/-
**IsLocalRing.ResidueField** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：ResidueField
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue field of a local ring is the quotient of the ring by its maximal ide
al.
-/
def ResidueField :=
  R ⧸ maximalIdeal R
deriving CommRing, Inhabited
/-
**IsLocalRing.ResidueField.field** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.ResidueF
ield`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → [inst_1 : IsLocalRing R] → Field (I
sLocalRing.ResidueField R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance ResidueField.field : Field (ResidueField R) :=
  fast_instance% Ideal.Quotient.field (maximalIdeal R)

/-- The quotient map from a local ring to its residue field. -/
/-
**IsLocalRing.residue** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：residue : R ->+* ResidueField R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map from a local ring to its residue field.
-/
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _

end IsLocalRing

