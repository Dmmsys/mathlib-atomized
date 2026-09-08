/-
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Qi Ge, Christian Merten
-/
module

public import Mathlib.RingTheory.RingHomProperties

/-! # Meta properties of injective ring homomorphisms -/

public section

/-
**_root_.RingHom.injective_stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.RingHom.injective_stableUnderComposition : RingHom.StableUnderCompo
sition (fun f => Function.Injective f)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingHom.injective_stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Injective f) := by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf
/-
**_root_.RingHom.injective_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.RingHom.injective_respectsIso : RingHom.RespectsIso (fun f => Funct
ion.Injective f)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingHom.injective_respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Injective f) := by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective
