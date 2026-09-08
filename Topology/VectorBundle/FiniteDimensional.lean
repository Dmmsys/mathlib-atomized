/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite-rank vector bundles -/

public section

namespace VectorBundle

open Bundle FiberBundle

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]

include E F

/-
**VectorBundle.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundle`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} (F : Type u_3) (E : B → Type u_4) [inst : 
NontriviallyNormedField R]   [inst_1 : TopologicalSpace B] [inst_2 : Topological
Space (Bundle.TotalSpace F E)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Norme
dSpace R F] [inst_5 : (x : B) → TopologicalSpace (E x)] [inst_6 : FiberBundle F 
E]   [inst_7 : (x : B) → AddCommGroup (E x)] [inst_8 : (x : B) → _root_.Module R
 (E x)] [VectorBundle R F E] (b : B)   [FiniteDimensional R F], FiniteDimensiona
l R (E b)
参数：R : Type u_1；F : Type u_3；E : B → Type u_4；Bundle.TotalSpace F E；x : B；E x；x 
: B；E x；x : B；E x；b : B；E b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
-/
protected lemma finiteDimensional (b : B) [FiniteDimensional R F] : FiniteDimensional R (E b) :=
  (continuousLinearEquivAt R F E b).symm.finiteDimensional
/-
**VectorBundle.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundle`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} (F : Type u_3) (E : B → Type u_4) [inst : 
NontriviallyNormedField R]   [inst_1 : TopologicalSpace B] [inst_2 : Topological
Space (Bundle.TotalSpace F E)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Norme
dSpace R F] [inst_5 : (x : B) → TopologicalSpace (E x)] [inst_6 : FiberBundle F 
E]   [inst_7 : (x : B) → AddCommGroup (E x)] [inst_8 : (x : B) → _root_.Module R
 (E x)] [VectorBundle R F E] (b : B),   Module.finrank R (E b) = Module.finrank 
R F
参数：R : Type u_1；F : Type u_3；E : B → Type u_4；Bundle.TotalSpace F E；x : B；E x；x 
: B；E x；x : B；E x；b : B；E b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
protected lemma finrank_eq (b : B) : Module.finrank R (E b) = Module.finrank R F :=
  (continuousLinearEquivAt R F E b).finrank_eq

end VectorBundle

