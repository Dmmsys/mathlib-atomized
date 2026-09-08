/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Maps.Strict.Group

/-!
# Strict linear maps

In this file, we study continuous linear maps which are *strict* in the sense of
`Topology.IsStrictMap`. So far, all the results in this file are direct
adaptations from the theory of strict homomorphisms of topological additive groups.
-/

@[expose] public section

open Topology

namespace LinearMap

variable {R S M N Nₗ M' Nₗ' : Type*} [Ring R] [Ring S] {σ : R →+* S}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup Nₗ] [AddCommGroup M'] [AddCommGroup Nₗ']
  [Module R M] [Module S N] [Module R Nₗ] [Module R M'] [Module R Nₗ']
  {f : M →ₛₗ[σ] N} {fₗ : M →ₗ[R] Nₗ} {gₗ : M' →ₗ[R] Nₗ'}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Nₗ]

/-- A linear map `f : M → N` is strict if and only if the induced map `M ⧸ f.ker → N` is an
embedding. -/
/-
**LinearMap.isStrictMap_iff_isEmbedding_liftQ_ker** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Ring
 R] [inst_1 : Ring S] {σ : R →+* S}   [inst_2 : AddCommGroup M] [inst_3 : AddCom
mGroup N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S N]   {f : M →ₛₗ
[σ] N} [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace N],   Topology.I
sStrictMap ⇑f ↔ Topology.IsEmbedding ⇑(f.ker.liftQ f ⋯)
参数：f.ker.liftQ f ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.isStrictMap_iff_isEmbedding_kerLift`：∀ {G : Type u_1} {H : 
Type u_2} [inst : AddGroup G] [inst_1 : AddGroup H] {f : G →+ H} [inst_2 : Topol
ogicalSpace G]   [inst_3 : Topological…

--- 原说明 ---
A linear map `f : M → N` is strict if and only if the induced map `M ⧸ f.ker → N
` is an
embedding.
-/
protected lemma isStrictMap_iff_isEmbedding_liftQ_ker :
    IsStrictMap f ↔ IsEmbedding (f.ker.liftQ f le_rfl) :=
  f.toAddMonoidHom.isStrictMap_iff_isEmbedding_kerLift

/-- A linear map `f : M → N` is strict if and only if the canonical isomorphism
`M ⧸ f.ker ≃ f.range` is a homeomorphism. -/
/-
**LinearMap.isStrictMap_iff_isHomeomorph_quotKerEquivRange** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {Nₗ : Type u_5} [inst : Ring R] [inst_1 : 
AddCommGroup M] [inst_2 : AddCommGroup Nₗ]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R Nₗ] {fₗ : M →ₗ[R] Nₗ} [inst_5 : TopologicalSpace M]   [inst_
6 : TopologicalSpace Nₗ], Topology.IsStrictMap ⇑fₗ ↔ IsHomeomorph ⇑fₗ.quotKerEqu
ivRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Topology.IsQuotientMap.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst
_2 : TopologicalSpace Z] {f …
· 使用定理 `Submodule.isQuotientMap_mkQ`：isQuotientMap_mkQ : IsQuotientMap S.mkQ
· 使用定理 `Topology.IsEmbedding.isStrictMap_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2
 : TopologicalSpace Z] {f …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A linear map `f : M → N` is strict if and only if the canonical isomorphism
`M ⧸ f.ker ≃ f.range` is a homeomorphism.
-/
protected lemma isStrictMap_iff_isHomeomorph_quotKerEquivRange :
    IsStrictMap fₗ ↔ IsHomeomorph fₗ.quotKerEquivRange := by
  -- Note: right now, this cannot easily be deduced from the `AddMonoidHom` statement, because
  -- `fₗ.quotKerEquivRange.toAddEquiv` is not def-eq to
  -- `QuotientAddGroup.quotientKerEquivRange fₗ.toAddMonoidHom`. This would require
  -- fixing the definition of `LinearMap.quotKerEquivRange`.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    fₗ.ker.isQuotientMap_mkQ.isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

/-- The isomorphism of topological modules `M ⧸ f.ker ≃ f.range` given by a strict linear
map `f : M → N`. This is an avatar of the first isomorphism theorem. -/
/-
**LinearMap._root_.ContinuousLinearEquiv.quotKerEquivRange** 是 Mathlib 中的一个定义，位于
命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of topological modules `M ⧸ f.ker ≃ f.range` given by a strict l
inear
map `f : M → N`. This is an avatar of the first isomorphism theorem.
-/
noncomputable def _root_.ContinuousLinearEquiv.quotKerEquivRange
    (hf : IsStrictMap fₗ) : (M ⧸ fₗ.ker) ≃L[R] fₗ.range :=
  .ofIsHomeomorph fₗ.quotKerEquivRange (fₗ.isStrictMap_iff_isHomeomorph_quotKerEquivRange.mp hf)

variable [IsTopologicalAddGroup M]

/-- A linear map is strict if and only if its `rangeRestrict` is an open quotient map. -/
/-
**LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Ring
 R] [inst_1 : Ring S] {σ : R →+* S}   [inst_2 : AddCommGroup M] [inst_3 : AddCom
mGroup N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S N]   {f : M →ₛₗ
[σ] N} [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace N] [IsTopologica
lAddGroup M]   [inst_9 : RingHomSurjective σ], Topology.IsStrictMap ⇑f ↔ IsOpenQ
uotientMap ⇑f.rangeRestrict
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict`：∀ {G : Typ
e u_1} {H : Type u_2} [inst : AddGroup G] [inst_1 : AddGroup H] {f : G →+ H} [in
st_2 : TopologicalSpace G]   [inst_3 : Topological…

--- 原说明 ---
A linear map is strict if and only if its `rangeRestrict` is an open quotient ma
p.
-/
protected lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict [RingHomSurjective σ] :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict :=
  f.toAddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict

variable [TopologicalSpace M'] [IsTopologicalAddGroup M'] [TopologicalSpace Nₗ']

/-- The product (in the sense of `LinearMap.prodMap`) of linear maps is strict if and only if both
maps are strict. -/
/-
**LinearMap.isStrictMap_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {Nₗ : Type u_5} {M' : Type u_6} {Nₗ' : Typ
e u_7} [inst : Ring R]   [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup Nₗ] [i
nst_3 : AddCommGroup M'] [inst_4 : AddCommGroup Nₗ']   [inst_5 : _root_.Module R
 M] [inst_6 : _root_.Module R Nₗ] [inst_7 : _root_.Module R M']   [inst_8 : _roo
t_.Module R Nₗ'] {fₗ : M →ₗ[R] Nₗ} {gₗ : M' →ₗ[R] Nₗ'} [inst_9 : TopologicalSpac
e M]   [inst_10 : TopologicalSpace Nₗ] [IsTopologicalAddGroup M] [inst_12 : Topo
logicalSpace M'] [IsTopologicalAddGroup M']   [inst_14 : TopologicalSpace Nₗ'], 
  Topology.IsStrictMap ⇑(fₗ.prodMap gₗ) ↔ Topology.IsStrictMap ⇑fₗ ∧ Topology.Is
StrictMap ⇑gₗ
参数：fₗ.prodMap gₗ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.isStrictMap_prodMap_iff`：∀ {G : Type u_1} {H : Type u_2} {G
' : Type u_3} {H' : Type u_4} [inst : AddGroup G'] [inst_1 : AddGroup H']   [ins
t_2 : AddGroup G] [inst_3 …

--- 原说明 ---
The product (in the sense of `LinearMap.prodMap`) of linear maps is strict if an
d only if both
maps are strict.
-/
protected lemma isStrictMap_prodMap_iff :
    IsStrictMap (fₗ.prodMap gₗ) ↔ IsStrictMap fₗ ∧ IsStrictMap gₗ :=
  AddMonoidHom.isStrictMap_prodMap_iff (f := fₗ.toAddMonoidHom) (g := gₗ.toAddMonoidHom)

/-- The product (in the sense of `LinearMap.prodMap`) of strict linear maps is strict. -/
/-
**LinearMap.isStrictMap_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {Nₗ : Type u_5} {M' : Type u_6} {Nₗ' : Typ
e u_7} [inst : Ring R]   [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup Nₗ] [i
nst_3 : AddCommGroup M'] [inst_4 : AddCommGroup Nₗ']   [inst_5 : _root_.Module R
 M] [inst_6 : _root_.Module R Nₗ] [inst_7 : _root_.Module R M']   [inst_8 : _roo
t_.Module R Nₗ'] {fₗ : M →ₗ[R] Nₗ} {gₗ : M' →ₗ[R] Nₗ'} [inst_9 : TopologicalSpac
e M]   [inst_10 : TopologicalSpace Nₗ] [IsTopologicalAddGroup M] [inst_12 : Topo
logicalSpace M'] [IsTopologicalAddGroup M']   [inst_14 : TopologicalSpace Nₗ'], 
  Topology.IsStrictMap ⇑fₗ → Topology.IsStrictMap ⇑gₗ → Topology.IsStrictMap ⇑(f
ₗ.prodMap gₗ)
参数：fₗ.prodMap gₗ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.isStrictMap_prodMap_iff`：∀ {R : Type u_1} {M : Type u_3} {Nₗ :
 Type u_5} {M' : Type u_6} {Nₗ' : Type u_7} [inst : Ring R]   [inst_1 : AddCommG
roup M] [inst_2 : AddCo…

--- 原说明 ---
The product (in the sense of `LinearMap.prodMap`) of strict linear maps is stric
t.
-/
protected lemma isStrictMap_prodMap (hf : IsStrictMap fₗ)
    (hg : IsStrictMap gₗ) : IsStrictMap (fₗ.prodMap gₗ) :=
  LinearMap.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

end LinearMap

