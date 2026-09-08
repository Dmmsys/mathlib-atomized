/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.GroupTheory.MonoidLocalization.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Affine monoids embed into `ℤⁿ`

This file proves that finitely generated cancellative torsion-free commutative monoids embed into
`ℤⁿ` for some `n`.
-/

public section

open Algebra AddLocalization Function

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineAddMonoid

variable (M) in
/-- The dimension of an affine monoid `M`, namely the minimum `n` for which `M` embeds into `ℤⁿ`. -/
/-
**AffineAddMonoid.dim** 是 Mathlib 中的一个缩写定义，位于命名空间 `AffineAddMonoid`。
形式化陈述：dim
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dimension of an affine monoid `M`, namely the minimum `n` for which `M` embe
ds into `ℤⁿ`.
-/
noncomputable abbrev dim := Module.finrank ℤ <| GrothendieckAddGroup M

variable (M) in
/-- An arbitrary embedding of an affine monoid `M` into `ℤ ^ dim M`. -/
/-
**AffineAddMonoid.embedding** 是 Mathlib 中的一个定义，位于命名空间 `AffineAddMonoid`。
形式化陈述：embedding : M ->+ FreeAbelianGroup (Fin (dim M))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary embedding of an affine monoid `M` into `ℤ ^ dim M`.
-/
noncomputable def embedding : M →+ FreeAbelianGroup (Fin (dim M)) :=
  .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom <|
    .comp (Module.finBasis ℤ _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom
/-
**AffineAddMonoid.embedding_injective** 是 Mathlib 中的一个引理，位于命名空间 `AffineAddMonoid
`。
形式化陈述：embedding_injective : Injective (embedding M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddLocalization.mk_left_injective`：∀ {α : Type u_1} [inst : AddCommMonoi
d α] [IsCancelAdd α] {s : AddSubmonoid α} (b : ↥s),   Function.Injective fun a =
> AddLocalization.mk a …
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
-/
lemma embedding_injective : Injective (embedding M) := by
  simpa [embedding] using! mk_left_injective 0

end AffineAddMonoid

