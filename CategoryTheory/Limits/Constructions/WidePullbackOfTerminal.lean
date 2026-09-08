/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Existence of wide pullbacks when the target object is terminal

In this file, we show that the wide pullback of a family of arrows `objs j ⟶ B`
exists when `B` is terminal and the product of the objects `objs j` exists.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {B : C} {objs : ι → C}
  (arrows : (j : ι) → objs j ⟶ B)

namespace WidePullbackCone

/-- The fan that is induced by a wide pullback cone. -/
/-
**CategoryTheory.Limits.WidePullbackCone.toFan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Limits.WidePullbackCone`。
形式化陈述：toFan (s : WidePullbackCone arrows) : Fan objs
参数：s : WidePullbackCone arrows。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fan that is induced by a wide pullback cone.
-/
abbrev toFan (s : WidePullbackCone arrows) : Fan objs :=
  Fan.mk _ s.π

variable (c : Fan objs)

/-- The wide pullback cone given by a fan, when the base object is terminal. -/
/-
**CategoryTheory.Limits.WidePullbackCone.ofFan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Limits.WidePullbackCone`。
形式化陈述：ofFan (hB : IsTerminal B) : WidePullbackCone arrows
参数：hB : IsTerminal B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The wide pullback cone given by a fan, when the base object is terminal.
-/
abbrev ofFan (hB : IsTerminal B) : WidePullbackCone arrows :=
  WidePullbackCone.mk (hB.from _) c.proj (fun _ ↦ hB.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
variable {c} in
/-- When the base object is terminal, a limit wide pullback cone can be obtained
from a limit fan. -/
/-
**CategoryTheory.Limits.WidePullbackCone.isLimitOfFan** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.WidePullbackCone`。
形式化陈述：isLimitOfFan (hc : IsLimit c) (hB : IsTerminal B) : IsLimit (ofFan arrows 
c hB)
参数：hc : IsLimit c；hB : IsTerminal B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the base object is terminal, a limit wide pullback cone can be obtained
from a limit fan.
-/
def isLimitOfFan (hc : IsLimit c) (hB : IsTerminal B) :
    IsLimit (ofFan arrows c hB) :=
  IsLimit.mk _
    (fun s ↦ hc.lift s.toFan)
    (fun s ↦ hB.hom_ext _ _)
    (fun s i ↦ hc.fac s.toFan (.mk i))
    (fun s m _ hm ↦ hc.hom_ext (fun ⟨i⟩ ↦ by simpa using! hm i))

end WidePullbackCone

/-
**CategoryTheory.Limits.hasWidePullback_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasWidePullback_of_isTerminal [HasProduct objs] (hB : IsTerminal B) : HasW
idePullback B objs arrows where exists_limit
参数：hB : IsTerminal B。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasWidePullback_of_isTerminal
    [HasProduct objs] (hB : IsTerminal B) :
    HasWidePullback B objs arrows where
  exists_limit :=
    ⟨_, WidePullbackCone.isLimitOfFan (arrows := arrows) (limit.isLimit _) hB⟩

end CategoryTheory.Limits

