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
/-- Noncomputable version of `Equiv.Perm.viaFintypeEmbedding` that does not assume `Fintype` -/
/-
**Equiv.Perm.viaEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：viaEmbedding : Perm β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun

--- 原说明 ---
Noncomputable version of `Equiv.Perm.viaFintypeEmbedding` that does not assume `
Fintype`
-/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)
/-
**Equiv.Perm.viaEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) := by
  classical
  exact extendDomain_apply_image e (ofInjective ι.1 ι.2) x
/-
**Equiv.Perm.viaEmbedding_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：viaEmbedding_apply_of_notMem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbeddi
ng ι x = x
参数：x : β；hx : x ∉ Set.range ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem viaEmbedding_apply_of_notMem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x := by
  classical
  exact extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

open scoped Classical in
/-- `viaEmbedding` as a group homomorphism -/
/-
**Equiv.Perm.viaEmbeddingHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：viaEmbeddingHom : Perm α ->* Perm β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun

--- 原说明 ---
`viaEmbedding` as a group homomorphism
-/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)
/-
**Equiv.Perm.viaEmbeddingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl
/-
**Equiv.Perm.viaEmbeddingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomainHom_injective`：extendDomainHom_injective : Functi
on.Injective (extendDomainHom f)
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) := by
  classical
  exact extendDomainHom_injective (ofInjective ι.1 ι.2)

end Perm

end Equiv

