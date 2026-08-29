/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.DenseEmbedding

/-!
# Additive characters of topological monoids
-/

public section

/--
lemma `DenseRange.addChar_eq_of_eval_one_eq` / 引理 `DenseRange.addChar_eq_of_eval_one_eq`

English:
lemma DenseRange.addChar_eq_of_eval_one_eq
  statement: {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A]
  proof: by
refine DFunLike.coe_injective hdr.equalizer hκ₁ hκ₂ (funext fun n => ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]

中文:
引理 DenseRange.addChar_eq_of_eval_one_eq
  结论: {A M : 类型} [TopologicalSpace A] [AddMonoidWithOne A]
  证明: by
refine DFunLike.coe_injective hdr.equalizer hκ₁ hκ₂ (funext fun n => ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]

Depends on / 依赖: AddChar, AddChar.map_nsmul_eq_pow, DFunLike, DFunLike.coe_injective, Function, Function.comp_apply, coe_injective, comp_apply, equalizer, hdr.equalizer, map_nsmul_eq_pow, nsmul_one
-/
lemma DenseRange.addChar_eq_of_eval_one_eq {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A]
    [Monoid M] [TopologicalSpace M] [T2Space M] (hdr : DenseRange ((↑) : Nat -> A))
    {κ₁ κ₂ : AddChar A M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous κ₂) (h : κ₁ 1 = κ₂ 1) :
    κ₁ = κ₂ := by
refine DFunLike.coe_injective hdr.equalizer hκ₁ hκ₂ (funext fun n => ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]
