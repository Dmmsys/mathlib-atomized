/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.UnivLE

/-!
# Universe inequalities and essential surjectivity of `uliftFunctor`.

We show `UnivLE.{max u v, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)`.
-/

@[expose] public section

open CategoryTheory

universe u v

noncomputable section

/--
theorem `UnivLE.ofEssSurj` / 定理 `UnivLE.ofEssSurj`

English:
theorem UnivLE.ofEssSurj
  given: (w : (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj)
  proof: by
    obtain ⟨a', m⟩ := w.mem_essImage α
    obtain ⟨m'⟩ := m
    exact ⟨a', ⟨(Iso.toEquiv m').symm.trans Equiv.ulift⟩⟩

中文:
定理 UnivLE.ofEssSurj
  条件: (w : (uliftFunctor.{u, v} : 类型v ⥤ 类型 最大值 u v).本质满射)
  证明: by
    obtain ⟨a', m⟩ := w.mem_essImage α
    obtain ⟨m'⟩ := m
    exact ⟨a', ⟨(Iso.toEquiv m').symm.trans Equiv.ulift⟩⟩

Depends on / 依赖: Equiv.ulift, Iso.toEquiv, mem_essImage, symm.trans, toEquiv, w.mem_essImage
-/
theorem UnivLE.ofEssSurj (w : (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj) :
    UnivLE.{max u v, v} where
  small α := by
    obtain ⟨a', m⟩ := w.mem_essImage α
    obtain ⟨m'⟩ := m
    exact ⟨a', ⟨(Iso.toEquiv m').symm.trans Equiv.ulift⟩⟩

/--
Instance `EssSurj.ofUnivLE` / 实例 `EssSurj.ofUnivLE`

English:
instance EssSurj.ofUnivLE
  signature: [UnivLE.{max u v, v}]
  body: ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

中文:
实例 本质满射.ofUnivLE
  签名: [UnivLE.{最大值 u v, v}]
  定义体: ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

Depends on / 依赖: Equiv.toIso, Equiv.ulift.trans, Shrink, equivShrink
-/
instance EssSurj.ofUnivLE [UnivLE.{max u v, v}] :
    (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj where
  mem_essImage α :=
    ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

/--
theorem `UnivLE_iff_essSurj` / 定理 `UnivLE_iff_essSurj`

English:
theorem UnivLE_iff_essSurj
  proof: ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩

中文:
定理 UnivLE_iff_essSurj
  证明: ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩

Depends on / 依赖: UnivLE, UnivLE.ofEssSurj, ofEssSurj
-/
theorem UnivLE_iff_essSurj :
    UnivLE.{max u v, v} ↔ (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj :=
  ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UnivLE.{max
  signature: u v, v}] : uliftFunctor.{u, v}.IsEquivalence where

中文:
实例 [UnivLE.{最大值
  签名: u v, v}] : uliftFunctor.{u, v}.是等价 where
-/
instance [UnivLE.{max u v, v}] : uliftFunctor.{u, v}.IsEquivalence where

/--
Definition of `UnivLE.witness` / `UnivLE.witness` 的定义

English:
definition UnivLE.witness
  signature: [UnivLE.{max u v, v}]
  body: uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

中文:
定义 UnivLE.witness
  签名: [UnivLE.{最大值 u v, v}]
  定义体: uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

Depends on / 依赖: uliftFunctor
-/
def UnivLE.witness [UnivLE.{max u v, v}] : Type u ⥤ Type v :=
  uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UnivLE.{max
  signature: u v, v}] : UnivLE.witness.{u, v}.Faithful
  body: inferInstanceAs Functor.Faithful (_ ⋙ _)

中文:
实例 [UnivLE.{最大值
  签名: u v, v}] : UnivLE.witness.{u, v}.忠实
  定义体: inferInstanceAs Functor.Faithful (_ ⋙ _)

Depends on / 依赖: Faithful, Functor, Functor.Faithful
-/
instance [UnivLE.{max u v, v}] : UnivLE.witness.{u, v}.Faithful :=
inferInstanceAs Functor.Faithful (_ ⋙ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UnivLE.{max
  signature: u v, v}] : UnivLE.witness.{u, v}.Full
  body: inferInstanceAs Functor.Full (_ ⋙ _)

中文:
实例 [UnivLE.{最大值
  签名: u v, v}] : UnivLE.witness.{u, v}.满
  定义体: inferInstanceAs Functor.Full (_ ⋙ _)

Depends on / 依赖: Functor, Functor.Full
-/
instance [UnivLE.{max u v, v}] : UnivLE.witness.{u, v}.Full :=
inferInstanceAs Functor.Full (_ ⋙ _)
