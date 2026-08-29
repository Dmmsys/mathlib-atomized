/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.IsConnected

/-!
# Filtered categories are connected
-/

public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
theorem `IsFilteredOrEmpty.isPreconnected` / 定理 `IsFilteredOrEmpty.isPreconnected`

English:
theorem IsFilteredOrEmpty.isPreconnected
  given: [IsFilteredOrEmpty C]
  statement: IsPreconnected C
  proof: zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

中文:
定理 IsFilteredOrEmpty.isPreconnected
  条件: [IsFilteredOrEmpty C]
  结论: IsPreconnected C
  证明: zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

Depends on / 依赖: IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, leftToMax, rightToMax, single, zigzag_isPreconnected
-/
theorem IsFilteredOrEmpty.isPreconnected [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

/--
theorem `IsCofilteredOrEmpty.isPreconnected` / 定理 `IsCofilteredOrEmpty.isPreconnected`

English:
theorem IsCofilteredOrEmpty.isPreconnected
  given: [IsCofilteredOrEmpty C]
  statement: IsPreconnected C
  proof: zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

中文:
定理 IsCofilteredOrEmpty.isPreconnected
  条件: [IsCofilteredOrEmpty C]
  结论: IsPreconnected C
  证明: zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

Depends on / 依赖: IsCofiltered, IsCofiltered.minToLeft, IsCofiltered.minToRight, minToLeft, minToRight, single, zigzag_isPreconnected
-/
theorem IsCofilteredOrEmpty.isPreconnected [IsCofilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

attribute [local instance] IsFiltered.nonempty in
/--
theorem `IsFiltered.isConnected` / 定理 `IsFiltered.isConnected`

English:
theorem IsFiltered.isConnected
  given: [IsFiltered C]
  statement: IsConnected C
  proof: { IsFilteredOrEmpty.isPreconnected C with }

中文:
定理 IsFiltered.isConnected
  条件: [IsFiltered C]
  结论: IsConnected C
  证明: { IsFilteredOrEmpty.isPreconnected C with }

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.isPreconnected, isPreconnected
-/
theorem IsFiltered.isConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.isPreconnected C with }

attribute [local instance] IsCofiltered.nonempty in
/--
theorem `IsCofiltered.isConnected` / 定理 `IsCofiltered.isConnected`

English:
theorem IsCofiltered.isConnected
  given: [IsCofiltered C]
  statement: IsConnected C
  proof: { IsCofilteredOrEmpty.isPreconnected C with }

中文:
定理 IsCofiltered.isConnected
  条件: [IsCofiltered C]
  结论: IsConnected C
  证明: { IsCofilteredOrEmpty.isPreconnected C with }

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.isPreconnected, isPreconnected
-/
theorem IsCofiltered.isConnected [IsCofiltered C] : IsConnected C :=
  { IsCofilteredOrEmpty.isPreconnected C with }

end CategoryTheory
