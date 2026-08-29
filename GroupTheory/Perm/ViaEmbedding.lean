/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# `Equiv.Perm.viaEmbedding`, a noncomputable analogue of `Equiv.Perm.viaFintypeEmbedding`.
-/

@[expose] public section


variable {α β : Type*}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open scoped Classical in
/--
Definition of `viaEmbedding` / `viaEmbedding` 的定义

English:
definition viaEmbedding
  signature: : Perm β
  body: extendDomain e (ofInjective ι.1 ι.2)

中文:
定义 viaEmbedding
  签名: : 置换 β
  定义体: extendDomain e (ofInjective ι.1 ι.2)

Depends on / 依赖: extendDomain, ofInjective
-/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)

/--
theorem `viaEmbedding_apply` / 定理 `viaEmbedding_apply`

English:
theorem viaEmbedding_apply
  given: (x : α)
  statement: e.viaEmbedding ι (ι x) = ι (e x)
  proof: by
  classical
  exact extendDomain_apply_image e (ofInjective ι.1 ι.2) x

中文:
定理 viaEmbedding_apply
  条件: (x : α)
  结论: e.viaEmbedding ι (ι x) = ι (e x)
  证明: by
  classical
  exact extendDomain_apply_image e (ofInjective ι.1 ι.2) x

Depends on / 依赖: classical, extendDomain_apply_image, ofInjective
-/
theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) := by
  classical
  exact extendDomain_apply_image e (ofInjective ι.1 ι.2) x

/--
theorem `viaEmbedding_apply_of_notMem` / 定理 `viaEmbedding_apply_of_notMem`

English:
theorem viaEmbedding_apply_of_notMem
  given: (x : β) (hx : x ∉ Set.range ι)
  statement: e.viaEmbedding ι x = x
  proof: by
  classical
  exact extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

中文:
定理 viaEmbedding_apply_of_notMem
  条件: (x : β) (hx : x ∉ 集合.range ι)
  结论: e.viaEmbedding ι x = x
  证明: by
  classical
  exact extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

Depends on / 依赖: classical, extendDomain_apply_not_subtype, ofInjective
-/
theorem viaEmbedding_apply_of_notMem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x := by
  classical
  exact extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

open scoped Classical in
/--
Definition of `viaEmbeddingHom` / `viaEmbeddingHom` 的定义

English:
definition viaEmbeddingHom
  signature: : Perm α ->* Perm β
  body: extendDomainHom (ofInjective ι.1 ι.2)

中文:
定义 viaEmbeddingHom
  签名: : 置换 α ->* 置换 β
  定义体: extendDomainHom (ofInjective ι.1 ι.2)

Depends on / 依赖: extendDomainHom, ofInjective
-/
noncomputable def viaEmbeddingHom : Perm α ->* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)

/--
theorem `viaEmbeddingHom_apply` / 定理 `viaEmbeddingHom_apply`

English:
theorem viaEmbeddingHom_apply
  statement: viaEmbeddingHom ι e = viaEmbedding e ι
  proof: rfl

中文:
定理 viaEmbeddingHom_apply
  结论: viaEmbeddingHom ι e = viaEmbedding e ι
  证明: rfl
-/
theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl

/--
theorem `viaEmbeddingHom_injective` / 定理 `viaEmbeddingHom_injective`

English:
theorem viaEmbeddingHom_injective
  statement: Function.Injective (viaEmbeddingHom ι)
  proof: by
  classical
  exact extendDomainHom_injective (ofInjective ι.1 ι.2)

中文:
定理 viaEmbeddingHom_injective
  结论: 函数.单射 (viaEmbeddingHom ι)
  证明: by
  classical
  exact extendDomainHom_injective (ofInjective ι.1 ι.2)

Depends on / 依赖: classical, extendDomainHom_injective, ofInjective
-/
theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) := by
  classical
  exact extendDomainHom_injective (ofInjective ι.1 ι.2)

end Perm

end Equiv
