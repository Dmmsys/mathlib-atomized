/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A module over a division ring is simple iff it has rank one
-/

public section

/-
**isSimpleModule_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleModule_iff_finrank_eq_one {R M} [DivisionRing R] [AddCommGroup M] 
[Module R M] : IsSimpleModule R M ↔ Module.finrank R M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.nontrivial`：IsSimpleModule.nontrivial [IsSimpleModule R M
] : Nontrivial M
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `IsSimpleModule.toSpanSingleton_surjective`：toSpanSingleton_surjective {m
 : M} (hm : m != 0) : Function.Surjective (toSpanSingleton R M m)
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `is_simple_module_of_finrank_eq_one`：is_simple_module_of_finrank_eq_one {
A} [Semiring A] [Module A V] [SMul K A] [IsScalarTower K A V] (h : finrank K V =
 1) : IsSimpleOrder (Sub…
-/
theorem isSimpleModule_iff_finrank_eq_one {R M} [DivisionRing R] [AddCommGroup M] [Module R M] :
    IsSimpleModule R M ↔ Module.finrank R M = 1 :=
  ⟨fun h ↦ have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩
