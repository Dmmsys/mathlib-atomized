/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!

# Characteristic of intermediate fields

This file contains some convenient instances for determining the characteristic of
intermediate fields. Some char zero instances are not provided, since they are already
covered by `SubsemiringClass.instCharZero`.

-/

public section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

namespace IntermediateField

variable (L : IntermediateField F E) (p : Nat)

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [CharZero F]
  body: charZero_of_injective_algebraMap (algebraMap F _).injective

中文:
实例 charZero
  签名: [CharZero F]
  定义体: charZero_of_injective_algebraMap (algebraMap F _).injective

Depends on / 依赖: algebraMap, charZero_of_injective_algebraMap, injective
-/
instance charZero [CharZero F] : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: [CharP F p]
  body: charP_of_injective_algebraMap (algebraMap F _).injective p

中文:
实例 charP
  签名: [CharP F p]
  定义体: charP_of_injective_algebraMap (algebraMap F _).injective p

Depends on / 依赖: algebraMap, charP_of_injective_algebraMap, injective
-/
instance charP [CharP F p] : CharP L p :=
  charP_of_injective_algebraMap (algebraMap F _).injective p

/--
Instance `expChar` / 实例 `expChar`

English:
instance expChar
  signature: [ExpChar F p]
  body: expChar_of_injective_algebraMap (algebraMap F _).injective p

中文:
实例 expChar
  签名: [ExpChar F p]
  定义体: expChar_of_injective_algebraMap (algebraMap F _).injective p

Depends on / 依赖: algebraMap, expChar_of_injective_algebraMap, injective
-/
instance expChar [ExpChar F p] : ExpChar L p :=
  expChar_of_injective_algebraMap (algebraMap F _).injective p

/--
Instance `charP'` / 实例 `charP'`

English:
instance charP'
  signature: [CharP E p]
  body: Subfield.charP L.toSubfield p

中文:
实例 charP'
  签名: [CharP E p]
  定义体: Subfield.charP L.toSubfield p

Depends on / 依赖: L.toSubfield, Subfield, Subfield.charP, toSubfield
-/
instance charP' [CharP E p] : CharP L p := Subfield.charP L.toSubfield p

/--
Instance `expChar'` / 实例 `expChar'`

English:
instance expChar'
  signature: [ExpChar E p]
  body: Subfield.expChar L.toSubfield p

中文:
实例 expChar'
  签名: [ExpChar E p]
  定义体: Subfield.expChar L.toSubfield p

Depends on / 依赖: L.toSubfield, Subfield, Subfield.expChar, expChar, toSubfield
-/
instance expChar' [ExpChar E p] : ExpChar L p := Subfield.expChar L.toSubfield p

end IntermediateField
