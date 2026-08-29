/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Purely inseparable ring homomorphisms

In this file we define purely inseparable ring homomorphisms and show their meta properties.

Since purely inseparable is mainly used for fields, we cannot prove many
general ring hom properties. E.g. we can't prove `StableUnderComposition IsPurelyInseparable`,
since `IsPurelyInseparable.trans` requires the involved rings to be fields.

-/

@[expose] public section

universe u v

/-- A ring homomorphism `f : F →+* E` is purely inseparable if `E` is purely inseparable as an
`F`-algebra. -/
@[algebraize IsPurelyInseparable]
/--
Definition of `RingHom.IsPurelyInseparable` / `RingHom.IsPurelyInseparable` 的定义

English:
definition RingHom.IsPurelyInseparable
  body: letI : Algebra F E := f.toAlgebra
  IsPurelyInseparable F E

中文:
定义 RingHom.IsPurelyInseparable
  定义体: letI : Algebra F E := f.toAlgebra
  IsPurelyInseparable F E
-/
protected def RingHom.IsPurelyInseparable
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] (f : F ->+* E) : Prop :=
  letI : Algebra F E := f.toAlgebra
  IsPurelyInseparable F E

/--
lemma `RingHom.isPurelyInseparable_algebraMap_iff` / 引理 `RingHom.isPurelyInseparable_algebraMap_iff`

English:
lemma RingHom.isPurelyInseparable_algebraMap_iff
  proof: by
  rw [RingHom.IsPurelyInseparable]; rw [toAlgebra_algebraMap]

中文:
引理 RingHom.isPurelyInseparable_algebraMap_iff
  证明: by
  rw [RingHom.IsPurelyInseparable]; rw [toAlgebra_algebraMap]

Depends on / 依赖: IsPurelyInseparable, RingHom, RingHom.IsPurelyInseparable, toAlgebra_algebraMap
-/
lemma RingHom.isPurelyInseparable_algebraMap_iff
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] [Algebra F E] :
    (algebraMap F E).IsPurelyInseparable ↔ IsPurelyInseparable F E := by
  rw [RingHom.IsPurelyInseparable]; rw [toAlgebra_algebraMap]

namespace RingHom.IsPurelyInseparable

variable {F E K : Type*}

variable (F) in
/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [CommRing F]
  statement: RingHom.IsPurelyInseparable (RingHom.id F)
  proof: isPurelyInseparable_self F

中文:
引理 id
  条件: [CommRing F]
  结论: RingHom.IsPurelyInseparable (RingHom.id F)
  证明: isPurelyInseparable_self F

Depends on / 依赖: isPurelyInseparable_self
-/
lemma id [CommRing F] : RingHom.IsPurelyInseparable (RingHom.id F) :=
  isPurelyInseparable_self F

/--
lemma `containsIdentities` / 引理 `containsIdentities`

English:
lemma containsIdentities
  statement: ContainsIdentities RingHom.IsPurelyInseparable
  proof: id

中文:
引理 containsIdentities
  结论: ContainsIdentities RingHom.IsPurelyInseparable
  证明: id
-/
lemma containsIdentities : ContainsIdentities RingHom.IsPurelyInseparable := id

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: [Field F] [Field E] [Field K] {f : F ->+* E} {g : E ->+* K}
  proof: by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.trans F E K

中文:
引理 comp
  结论: [Field F] [Field E] [Field K] {f : F ->+* E} {g : E ->+* K}
  证明: by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.trans F E K

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.trans, algebraize, g.comp
-/
lemma comp [Field F] [Field E] [Field K] {f : F ->+* E} {g : E ->+* K}
    (hf : f.IsPurelyInseparable) (hg : g.IsPurelyInseparable) :
    (g.comp f).IsPurelyInseparable := by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.trans F E K

end RingHom.IsPurelyInseparable
