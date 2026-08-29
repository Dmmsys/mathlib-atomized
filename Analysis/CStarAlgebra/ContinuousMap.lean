/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # C⋆-algebras of continuous functions

We place these here because, for reasons related to the import hierarchy, they cannot be placed in
earlier files.
-/

public section

variable {α A : Type*}
noncomputable section

namespace BoundedContinuousFunction

variable [TopologicalSpace α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] : NonUnitalCStarAlgebra (α ->ᵇ A) where

中文:
实例 [非幺CStar代数
  签名: A] : 非幺CStar代数 (α ->ᵇ A) where
-/
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α ->ᵇ A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommCStarAlgebra
  signature: A] : NonUnitalCommCStarAlgebra (α ->ᵇ A) where

中文:
实例 [非幺交换CStar代数
  签名: A] : 非幺交换CStar代数 (α ->ᵇ A) where
-/
instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α ->ᵇ A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] : CStarAlgebra (α ->ᵇ A) where

中文:
实例 [CStar代数
  签名: A] : CStar代数 (α ->ᵇ A) where
-/
instance [CStarAlgebra A] : CStarAlgebra (α ->ᵇ A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommCStarAlgebra
  signature: A] : CommCStarAlgebra (α ->ᵇ A) where

中文:
实例 [交换CStar代数
  签名: A] : 交换CStar代数 (α ->ᵇ A) where
-/
instance [CommCStarAlgebra A] : CommCStarAlgebra (α ->ᵇ A) where

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] : NonUnitalCStarAlgebra C(α, A) where

中文:
实例 [非幺CStar代数
  签名: A] : 非幺CStar代数 C(α, A) where
-/
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommCStarAlgebra
  signature: A] : NonUnitalCommCStarAlgebra C(α, A) where

中文:
实例 [非幺交换CStar代数
  签名: A] : 非幺交换CStar代数 C(α, A) where
-/
instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] : CStarAlgebra C(α, A) where

中文:
实例 [CStar代数
  签名: A] : CStar代数 C(α, A) where
-/
instance [CStarAlgebra A] : CStarAlgebra C(α, A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommCStarAlgebra
  signature: A] : CommCStarAlgebra C(α, A) where

中文:
实例 [交换CStar代数
  签名: A] : 交换CStar代数 C(α, A) where
-/
instance [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) where

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where

中文:
实例 [拓扑空间
  签名: α] [非幺CStar代数 A] : 非幺CStar代数 C₀(α, A) where
-/
instance [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [NonUnitalCommCStarAlgebra A] :

中文:
实例 [拓扑空间
  签名: α] [非幺交换CStar代数 A] :
-/
instance [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) where

end ZeroAtInftyContinuousMap
