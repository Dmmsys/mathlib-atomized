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
  {ι : Type w} {B : C} {objs : ι -> C}
  (arrows : (j : ι) -> objs j ⟶ B)

namespace WidePullbackCone

/--
Definition of `toFan` / `toFan` 的定义

English:
abbreviation toFan
  signature: (s : WidePullbackCone arrows)
  body: Fan.mk _ s.π

中文:
缩写 toFan
  签名: (s : WidePullbackCone arrows)
  定义体: Fan.mk _ s.π

Depends on / 依赖: Fan.mk
-/
abbrev toFan (s : WidePullbackCone arrows) : Fan objs :=
  Fan.mk _ s.π

variable (c : Fan objs)

/--
Definition of `ofFan` / `ofFan` 的定义

English:
abbreviation ofFan
  signature: (hB : IsTerminal B)
  body: WidePullbackCone.mk (hB.from _) c.proj (fun _ => hB.hom_ext _ _)

中文:
缩写 ofFan
  签名: (hB : IsTerminal B)
  定义体: WidePullbackCone.mk (hB.from _) c.proj (fun _ => hB.hom_ext _ _)

Depends on / 依赖: WidePullbackCone, WidePullbackCone.mk, c.proj, hB.from, hB.hom_ext, hom_ext
-/
abbrev ofFan (hB : IsTerminal B) : WidePullbackCone arrows :=
  WidePullbackCone.mk (hB.from _) c.proj (fun _ => hB.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
variable {c} in
/--
Definition of `isLimitOfFan` / `isLimitOfFan` 的定义

English:
definition isLimitOfFan
  signature: (hc : IsLimit c) (hB : IsTerminal B)
  body: IsLimit.mk _
    (fun s => hc.lift s.toFan)
    (fun s => hB.hom_ext _ _)
    (fun s i => hc.fac s.toFan (.mk i))
    (fun s m _ hm => hc.hom_ext (fun ⟨i⟩ => by simpa using! hm i))

中文:
定义 isLimitOfFan
  签名: (hc : IsLimit c) (hB : IsTerminal B)
  定义体: IsLimit.mk _
    (fun s => hc.lift s.toFan)
    (fun s => hB.hom_ext _ _)
    (fun s i => hc.fac s.toFan (.mk i))
    (fun s m _ hm => hc.hom_ext (fun ⟨i⟩ => by simpa using! hm i))

Depends on / 依赖: IsLimit, IsLimit.mk, hB.hom_ext, hc.fac, hc.hom_ext, hc.lift, hom_ext, s.toFan
-/
def isLimitOfFan (hc : IsLimit c) (hB : IsTerminal B) :
    IsLimit (ofFan arrows c hB) :=
  IsLimit.mk _
    (fun s => hc.lift s.toFan)
    (fun s => hB.hom_ext _ _)
    (fun s i => hc.fac s.toFan (.mk i))
    (fun s m _ hm => hc.hom_ext (fun ⟨i⟩ => by simpa using! hm i))

end WidePullbackCone

/--
lemma `hasWidePullback_of_isTerminal` / 引理 `hasWidePullback_of_isTerminal`

English:
lemma hasWidePullback_of_isTerminal
  proof: ⟨_, WidePullbackCone.isLimitOfFan (arrows := arrows) (limit.isLimit _) hB⟩

中文:
引理 hasWidePullback_of_isTerminal
  证明: ⟨_, WidePullbackCone.isLimitOfFan (arrows := arrows) (limit.isLimit _) hB⟩

Depends on / 依赖: WidePullbackCone, WidePullbackCone.isLimitOfFan, arrows, isLimit, isLimitOfFan, limit.isLimit
-/
lemma hasWidePullback_of_isTerminal
    [HasProduct objs] (hB : IsTerminal B) :
    HasWidePullback B objs arrows where
  exists_limit :=
    ⟨_, WidePullbackCone.isLimitOfFan (arrows := arrows) (limit.isLimit _) hB⟩

end CategoryTheory.Limits
