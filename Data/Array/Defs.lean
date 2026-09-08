/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions.
-/

deprecated_module (since := "2026-03-05")

@[expose] public section

namespace Array

universe u
variable {α : Type u}

/-- Permute the array using a sequence of indices defining a cyclic permutation.
  If the list of indices `l = [i₁, i₂, ..., iₙ]` are all distinct then
  `(cyclicPermute! a l)[iₖ₊₁] = a[iₖ]` and `(cyclicPermute! a l)[i₀] = a[iₙ]` -/
@[deprecated "This is now in `Mathlib.Tactic.Translate.Reorder.permute!`" (since := "2026-03-05")]
/-
**Array.cyclicPermute** 是 Mathlib 中的一个定义，位于命名空间 `Array`。
形式化陈述：cyclicPermute! [Inhabited α] : Array α -> List Nat -> Array α | a, [] => a
 | a, i :: is => cyclicPermuteAux a is a[i]! i where cyclicPermuteAux : Array α 
-> List Nat -> α -> Nat -> Array α | a, [], x, i0 => a.set! i0 x | a, i :: is, x
, i0 => let (y, a)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Permute the array using a sequence of indices defining a cyclic permutation.
  If the list of indices `l = [i₁, i₂, ..., iₙ]` are all distinct then
  `(cyclicPermute! a l)[iₖ₊₁] = a[iₖ]` and `(cyclicPermute! a l)[i₀] = a[iₙ]`
-/
def cyclicPermute! [Inhabited α] : Array α → List Nat → Array α
  | a, [] => a
  | a, i :: is => cyclicPermuteAux a is a[i]! i
where cyclicPermuteAux : Array α → List Nat → α → Nat → Array α
| a, [], x, i0 => a.set! i0 x
| a, i :: is, x, i0 =>
  let (y, a) := a.swapAt! i x
  cyclicPermuteAux a is y i0

/-- Permute the array using a list of cycles. -/
@[deprecated "This is now in `Mathlib.Tactic.Translate.Reorder.permute!`" (since := "2026-03-05")]
/-
**Array.permute** 是 Mathlib 中的一个定义，位于命名空间 `Array`。
形式化陈述：permute! [Inhabited α] (a : Array α) (ls : List (List Nat)) : Array α
参数：a : Array α；ls : List (List Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Permute the array using a list of cycles.
-/
def permute! [Inhabited α] (a : Array α) (ls : List (List Nat)) : Array α :=
ls.foldl (init := a) (·.cyclicPermute! ·)

end Array

