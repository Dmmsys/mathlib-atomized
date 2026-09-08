/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Max
public import Mathlib.Data.Set.CoeSort

/-!
# Maximal elements of subsets

Let `S : Set J` and `m : S`. If `m` is not a maximal element of `S`,
then `↑m : J` is not maximal in `J`.

-/

public section

universe u

namespace Set

variable {J : Type u} [Preorder J] {S : Set J} (m : S)

/-
**Set.not_isMax_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_isMax_coe (hm : ¬ IsMax m) : ¬ IsMax m.1
参数：hm : ¬ IsMax m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_isMax_coe (hm : ¬ IsMax m) :
    ¬ IsMax m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)
/-
**Set.not_isMin_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_isMin_coe (hm : ¬ IsMin m) : ¬ IsMin m.1
参数：hm : ¬ IsMin m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_isMin_coe (hm : ¬ IsMin m) :
    ¬ IsMin m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)

end Set

