/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!

# Compact submodules

-/

public section

variable {R M : Type*} [CommSemiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]

/-
**Submodule.isCompact_of_fg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.isCompact_of_fg [CompactSpace R] {N : Submodule R M} (hN : N.FG)
 : IsCompact (X
参数：hN : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.range_linearCombination`：Fintype.range_linearCombination : Linea
rMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma Submodule.isCompact_of_fg [CompactSpace R] {N : Submodule R M} (hN : N.FG) :
    IsCompact (X := M) N := by
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  fun_prop
/-
**Ideal.isCompact_of_fg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isCompact_of_fg [IsTopologicalSemiring R] [CompactSpace R] {I : Idea
l R} (hI : I.FG) : IsCompact (X
参数：hI : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.isCompact_of_fg`：Submodule.isCompact_of_fg [CompactSpace R] {N
 : Submodule R M} (hN : N.FG) : IsCompact (X
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
-/
lemma Ideal.isCompact_of_fg [IsTopologicalSemiring R] [CompactSpace R]
    {I : Ideal R} (hI : I.FG) : IsCompact (X := R) I :=
  Submodule.isCompact_of_fg hI

variable (R M) in
/-
**Module.Finite.compactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Finite.compactSpace [CompactSpace R] [Module.Finite R M] : CompactS
pace M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.isCompact_of_fg`：Submodule.isCompact_of_fg [CompactSpace R] {N
 : Submodule R M} (hN : N.FG) : IsCompact (X
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
lemma Module.Finite.compactSpace [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) IsNoetherianRing.isClosed_ideal
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsNoetherianRing R] [CompactSpace R] [T2Space R] (I : Ideal R) :
    IsClosed (X := R) I :=
  (Ideal.isCompact_of_fg (IsNoetherian.noetherian I)).isClosed
