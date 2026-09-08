/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.RootPositive
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.RepresentationTheory.Submodule

/-!
# Irreducible root pairings

This file contains basic definitions and results about irreducible root systems.

## Main definitions / results:
* `RootPairing.isSimpleModule_weylGroupRootRep_iff`: a criterion for the representation of the Weyl
  group on root space to be irreducible.
* `RootPairing.IsIrreducible`: a typeclass encoding the fact that a root pairing is irreducible.
* `RootPairing.IsIrreducible.mk'`: an alternative constructor for irreducibility when the
  coefficients are a field.

-/

@[expose] public section

open Function Set
open Submodule (span span_le)
open LinearMap (ker)
open MulAction (orbit mem_orbit_self mem_orbit_iff)
open Module.End (invtSubmodule)
open scoped MonoidAlgebra

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/-- The sublattice of invariant submodules of the root space. -/
/-
**RootPairing.invtRootSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：invtRootSubmodule : Sublattice (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sublattice of invariant submodules of the root space.
-/
def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)
/-
**RootPairing.mem_invtRootSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：mem_invtRootSubmodule_iff {q : Submodule R M} : q in P.invtRootSubmodule ↔
 forall i, q in Module.End.invtSubmodule (P.reflection i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q ∈ P.invtRootSubmodule ↔ ∀ i, q ∈ Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]
/-
**RootPairing.invtRootSubmodule.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.i
nvtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⊤ ∈ P.invtR
ootSubmodule
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma invtRootSubmodule.top_mem : ⊤ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]
/-
**RootPairing.invtRootSubmodule.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.i
nvtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⊥ ∈ P.invtR
ootSubmodule
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma invtRootSubmodule.bot_mem : ⊥ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder P.invtRootSubmodule where
  top := ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nontrivial P.invtRootSubmodule where
  exists_pair_ne := ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩
/-
**RootPairing.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N), ↑⊥ = ⊥
参数：P : RootPairing ι R M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl
/-
**RootPairing.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N), ↑⊤ = ⊤
参数：P : RootPairing ι R M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl
/-
**RootPairing.eq_zero_iff_forall_coroot'_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Root
Pairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [P.IsRootSys
tem] {x : M}, x = 0 ↔ ∀ (i : ι), (P.coroot' i) x = 0
参数：P : RootPairing ι R M N；i : ι；P.coroot' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'`：corootSp
an_dualAnnihilator_map_eq_iInf_ker_coroot' : (P.corootSpan R).dualAnnihilator.ma
p (P.toPerfPair.symm : Dual R N ->ₗ[R] M) = ⨅ i, (P.…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `RootPairing.IsRootSystem.span_coroot_eq_top`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
-/
lemma eq_zero_iff_forall_coroot'_eq_zero [P.IsRootSystem] {x : M} :
    x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  replace h : x ∈ ⨅ i, ker (P.coroot' i) := by aesop
  simpa [← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] using h
/-
**RootPairing.invtRootSubmodule.le_ker_coroot'** 是 Mathlib 中的一个定理，位于命名空间 `RootPa
iring.invtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] {K : Type u_5}   [inst_2 : Field K] [NeZero 2] [inst_4 : 
_root_.Module K M] [inst_5 : _root_.Module K N] {P : RootPairing ι K M N}   (q :
 ↥P.invtRootSubmodule) {k : ι}, P.root k ∉ ↑q → ↑q ≤ LinearMap.ker (P.coroot' k)
参数：q : ↥P.invtRootSubmodule；P.coroot' k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
· 使用定理 `Submodule.mem_invtSubmodule_reflection_iff`：∀ {R : Type u_1} {M : Type u
_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {
x : M}   {f : Module.Dual R M} […
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `Submodule.disjoint_span_singleton_of_notMem`：disjoint_span_singleton_of_
notMem (hx : x ∉ s) : Disjoint s (K ∙ x)
· 使用引理 `RootPairing.mem_invtRootSubmodule_iff`：mem_invtRootSubmodule_iff {q : Su
bmodule R M} : q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodul
e (P.reflection i)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma invtRootSubmodule.le_ker_coroot' {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N}
    (q : P.invtRootSubmodule) {k : ι} (hk : P.root k ∉ (q : Submodule K M)) :
    (q : Submodule K M) ≤ LinearMap.ker (P.coroot' k) :=
  (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two k)
    (Submodule.disjoint_span_singleton_of_notMem hk)).mp
    (P.mem_invtRootSubmodule_iff.mp q.property k)
/-
**RootPairing.invtRootSubmodule.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `RootPairin
g.invtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] {K : Type u_5}   [inst_2 : Field K] [NeZero 2] [inst_4 : 
_root_.Module K M] [inst_5 : _root_.Module K N] {P : RootPairing ι K M N}   [P.I
sRootSystem] (q : ↥P.invtRootSubmodule), q = ⊥ ↔ ∀ (i : ι), P.root i ∉ ↑q
参数：q : ↥P.invtRootSubmodule；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.mk_eq_bot_iff`：mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)]
 (hbot : p ⊥) {x : α} (hx : p x) : (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥
· 使用定理 `RootPairing.invtRootSubmodule.bot_mem`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RootPairing.eq_zero_iff_forall_coroot'_eq_zero`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.invtRootSubmodule.le_ker_coroot'`：∀ {ι : Type u_1} {M : Type
 u_3} {N : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] {K : Type
 u_5}   [inst_2 : Field K] [NeZero…
-/
lemma invtRootSubmodule.eq_bot_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊥ ↔ ∀ i, P.root i ∉ (q : Submodule K M) := by
  refine ⟨fun h ↦ by simp [h, P.ne_zero], fun h ↦ ?_⟩
  simp_rw [Subtype.mk_eq_bot_iff (invtRootSubmodule.bot_mem P), Submodule.eq_bot_iff,
    P.eq_zero_iff_forall_coroot'_eq_zero, ← LinearMap.mem_ker]
  exact fun x hx i ↦ invtRootSubmodule.le_ker_coroot' q (h i) hx
/-
**RootPairing.invtRootSubmodule.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `RootPairin
g.invtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] {K : Type u_5}   [inst_2 : Field K] [inst_3 : _root_.Modu
le K M] [inst_4 : _root_.Module K N] {P : RootPairing ι K M N}   [P.IsRootSystem
] (q : ↥P.invtRootSubmodule), q = ⊤ ↔ Set.range ⇑P.root ⊆ ↑↑q
参数：q : ↥P.invtRootSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [Module K M] [Module K N]
    {P : RootPairing ι K M N} [P.IsRootSystem] (q : P.invtRootSubmodule) :
    q = ⊤ ↔ range P.root ⊆ q :=
  ⟨fun h ↦ by simp [h], fun h ↦ by simpa using Submodule.span_mono h (R := K)⟩
/-
**RootPairing.invtRootSubmodule.eq_span_root** 是 Mathlib 中的一个定理，位于命名空间 `RootPair
ing.invtRootSubmodule`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] {K : Type u_5}   [inst_2 : Field K] [NeZero 2] [inst_4 : 
_root_.Module K M] [inst_5 : _root_.Module K N] {P : RootPairing ι K M N}   [P.I
sRootSystem] (q : ↥P.invtRootSubmodule), ↑q = Submodule.span K (⇑P.root '' {i | 
P.root i ∈ ↑q})
参数：q : ↥P.invtRootSubmodule；⇑P.root '' {i | P.root i ∈ ↑q}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `RootPairing.root_coroot'_eq_pairing`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用引理 `RootPairing.pairing_eq_zero_iff'`：pairing_eq_zero_iff' [NeZero (2 : R)] 
[IsDomain R] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RootPairing.invtRootSubmodule.le_ker_coroot'`：∀ {ι : Type u_1} {M : Type
 u_3} {N : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] {K : Type
 u_5}   [inst_2 : Field K] [NeZero…
（共 32 条，此处仅展示前 30 条）
-/
lemma invtRootSubmodule.eq_span_root {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    (q : Submodule K M) = span K (P.root '' {i | P.root i ∈ (q : Submodule K M)}) := by
  set Q := (q : Submodule K M)
  have hSQ : span K (P.root '' {i | P.root i ∈ Q}) ≤ Q :=
    span_le.mpr (Set.image_subset_iff.mpr fun _ h => h)
  refine le_antisymm ?_ hSQ
  set S := span K (P.root '' {i | P.root i ∈ Q})
  set T := span K (P.root '' {i | P.root i ∉ Q})
  have h_sup : S ⊔ T = ⊤ := by
    rw [← Submodule.span_union, ← Set.image_union]
    have : {i | P.root i ∈ Q} ∪ {i | P.root i ∉ Q} = Set.univ := by ext; simp [em]
    rw [this, Set.image_univ]
    simp
  intro v hv
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h_sup ▸ Submodule.mem_top (x := v))
  suffices t = 0 by rw [this, add_zero]; exact hs
  have htQ : t ∈ Q := by simpa using Q.sub_mem hv (hSQ hs)
  have h_ker : ∀ k, P.coroot' k t = 0 := by
    intro k
    by_cases hk : P.root k ∈ Q
    · refine LinearMap.mem_ker.mp (span_le.mpr ?_ ht)
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, P.root_coroot'_eq_pairing, P.pairing_eq_zero_iff',
        ← P.root_coroot'_eq_pairing]
      exact LinearMap.mem_ker.mp (invtRootSubmodule.le_ker_coroot' q hj hk)
    · exact LinearMap.mem_ker.mp (invtRootSubmodule.le_ker_coroot' q hk htQ)
  exact P.eq_zero_iff_forall_coroot'_eq_zero.mpr h_ker
/-
**RootPairing.isSimpleModule_weylGroupRootRep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：isSimpleModule_weylGroupRootRep_iff [Nontrivial M] : IsSimpleModule R[P.we
ylGroup] P.weylGroupRootRep.asModule ↔ forall (q : Submodule R M), (forall i, q 
in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
· 使用定理 `RootPairing.weylGroup.induction`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 :
 _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Module.End.invtSubmodule.one`：∀ {R : Type u_1} {M : Type u_2} [inst : Se
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.End.
invtSubmodule 1 = …
· 使用定理 `Module.End.invtSubmodule.comp`：∀ {R : Type u_1} {M : Type u_2} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module
.End R M) {p : Subm…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Representation.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule k V} 
: p in ρ.invtSubmodule ↔ forall g, p in Module.End.invtSubmodule (ρ g)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Representation.invtSubmodule.instNontrivialSubtypeSubmoduleMemSublattice
`：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1
 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Mod…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `RootPairing.reflection_mem_weylGroup`：reflection_mem_weylGroup : Equiv.r
eflection P i in P.weylGroup
-/
lemma isSimpleModule_weylGroupRootRep_iff [Nontrivial M] :
    IsSimpleModule R[P.weylGroup] P.weylGroupRootRep.asModule ↔
    ∀ (q : Submodule R M), (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤ := by
  rw [isSimpleModule_iff, ← P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun h q hq₁ hq₂ ↦ ?_, fun h ↦ ⟨fun q ↦ ?_⟩⟩
  · suffices ∀ g : P.weylGroup, q ∈ invtSubmodule (P.weylGroupRootRep g) by
      let q' : P.weylGroupRootRep.invtSubmodule :=
        ⟨q, (Representation.mem_invtSubmodule P.weylGroupRootRep).mpr this⟩
      suffices q' = ⊤ by simpa [q']
      apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
      simpa [q']
    rintro ⟨g, hg⟩
    induction hg using weylGroup.induction with
    | mem i => exact hq₁ i
    | one => simp [← Submonoid.one_def]
    | mul x y hx hy hx' hy' => apply invtSubmodule.comp <;> assumption
  · rcases eq_or_ne q ⊥ with rfl | hq; · tauto
    suffices (q : Submodule R M) = ⊤ by right; simpa using this
    refine h q (fun i ↦ ?_) (by simpa using hq)
    exact P.weylGroupRootRep.mem_invtSubmodule.mp q.property ⟨_, P.reflection_mem_weylGroup i⟩

/-- A root pairing is irreducible if it is non-trivial and contains no proper invariant submodules.
-/
/-
**RootPairing.IsIrreducible** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root pairing is irreducible if it is non-trivial and contains no proper invari
ant submodules.
-/
@[mk_iff] class IsIrreducible : Prop where
  nontrivial : Nontrivial M
  nontrivial' : Nontrivial N
  eq_top_of_invtSubmodule_reflection (q : Submodule R M) :
    (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤
  eq_top_of_invtSubmodule_coreflection (q : Submodule R N) :
    (∀ i, q ∈ invtSubmodule (P.coreflection i)) → q ≠ ⊥ → q = ⊤
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsIrreducible] : P.flip.IsIrreducible where
  nontrivial := IsIrreducible.nontrivial' P
  nontrivial' := IsIrreducible.nontrivial P
  eq_top_of_invtSubmodule_reflection := IsIrreducible.eq_top_of_invtSubmodule_coreflection (P := P)
  eq_top_of_invtSubmodule_coreflection := IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P)
/-
**RootPairing.isSimpleModule_weylGroupRootRep** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：isSimpleModule_weylGroupRootRep [P.IsIrreducible] : IsSimpleModule R[P.wey
lGroup] P.weylGroupRootRep.asModule
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsIrreducible.nontrivial`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {ins
t_2 : _root_.Module R M} {…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.isSimpleModule_weylGroupRootRep_iff`：isSimpleModule_weylGrou
pRootRep_iff [Nontrivial M] : IsSimpleModule R[P.weylGroup] P.weylGroupRootRep.a
sModule ↔ forall (q : Submodule R M),…
· 使用定理 `RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection`：∀ {ι : Typ
e u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 
: AddCommGroup M}   {inst_2 : _root_.Module R M} {…
-/
lemma isSimpleModule_weylGroupRootRep [P.IsIrreducible] :
    IsSimpleModule R[P.weylGroup] P.weylGroupRootRep.asModule :=
  have := IsIrreducible.nontrivial P
  P.isSimpleModule_weylGroupRootRep_iff.mpr IsIrreducible.eq_top_of_invtSubmodule_reflection

@[nontriviality]
/-
**RootPairing.not_isIrreducible_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：not_isIrreducible_of_subsingleton [Subsingleton M] : ¬ P.IsIrreducible
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nontrivial`：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
· 使用定理 `RootPairing.IsIrreducible.nontrivial`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {ins
t_2 : _root_.Module R M} {…
-/
lemma not_isIrreducible_of_subsingleton [Subsingleton M] :
    ¬ P.IsIrreducible :=
  fun contra ↦ not_nontrivial _ contra.nontrivial

/-- A nonempty irreducible root pairing is a root system. -/
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty irreducible root pairing is a root system.
-/
instance [Nonempty ι] [NeZero (2 : R)] [P.IsIrreducible] : P.IsRootSystem where
  span_root_eq_top := IsIrreducible.eq_top_of_invtSubmodule_reflection
    (P.rootSpan R) P.rootSpan_mem_invtSubmodule_reflection (P.rootSpan_ne_bot R)
  span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
    (P.corootSpan R) P.corootSpan_mem_invtSubmodule_coreflection (P.corootSpan_ne_bot R)
/-
**RootPairing.invtSubmodule_reflection_of_invtSubmodule_coreflection** 是 Mathlib
 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：invtSubmodule_reflection_of_invtSubmodule_coreflection (i : ι) (q : Submod
ule R N) (hq : q in invtSubmodule (P.coreflection i)) : q.dualAnnihilator.map (P
.toPerfPair.symm : Module.Dual R N ->ₗ[R] M) in invtSubmodule (P.reflection i)
参数：i : ι；q : Submodule R N；hq : q in invtSubmodule (P.coreflection i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_mem_invtSubmodule_iff`：∀ {R : Type u_3} {M : Type u_4} {
N : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _ro
ot_.Module R M] [inst_3 : A…
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用引理 `RootPairing.toPerfPair_conj_reflection`：toPerfPair_conj_reflection : P.t
oPerfPair.conj (P.reflection i) = (P.coreflection i).toLinearMap.dualMap
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Submodule.dualAnnihilator_map_dualMap_le`：dualAnnihilator_map_dualMap_le
 {N : Type*} [AddCommMonoid N] [Module R N] (W : Submodule R M) (f : N ->ₗ[R] M)
 : W.dualAnnihilator.map f.dua…
· 使用定理 `Submodule.dualAnnihilator_anti`：dualAnnihilator_anti {U V : Submodule R 
M} (hUV : U <= V) : V.dualAnnihilator <= U.dualAnnihilator
-/
lemma invtSubmodule_reflection_of_invtSubmodule_coreflection (i : ι) (q : Submodule R N)
    (hq : q ∈ invtSubmodule (P.coreflection i)) :
    q.dualAnnihilator.map (P.toPerfPair.symm : Module.Dual R N →ₗ[R] M) ∈
      invtSubmodule (P.reflection i) := by
  rw [LinearEquiv.map_mem_invtSubmodule_iff, LinearEquiv.symm_symm, toPerfPair_conj_reflection,
    Module.End.mem_invtSubmodule, ← Submodule.map_le_iff_le_comap]
  exact (Submodule.dualAnnihilator_map_dualMap_le _ _).trans <| Submodule.dualAnnihilator_anti hq

/-- When the coefficients are a field, the coroot conditions for irreducibility follow from those
for the roots. -/
/-
**RootPairing.IsIrreducible.mk'** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsIrreduc
ible`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] {K : Type u_5}   [inst_2 : Field K] [inst_3 : _root_.Modu
le K M] [inst_4 : _root_.Module K N] [Nontrivial M] (P : RootPairing ι K M N),  
 (∀ (q : Submodule K M), (∀ (i : ι), q ∈ Module.End.invtSubmodule ↑(P.reflection
 i)) → q ≠ ⊥ → q = ⊤) → P.IsIrreducible
参数：P : RootPairing ι K M N；∀ (q : Submodule K M), (∀ (i : ι), q ∈ Module.End.inv
tSubmodule ↑(P.reflection i)) → q ≠ ⊥ → q = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.nontrivial_dual_iff`：nontrivial_dual_iff : Nontrivial (Dual K V) 
↔ Nontrivial V
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Submodule.map_eq_top_iff`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用引理 `RootPairing.invtSubmodule_reflection_of_invtSubmodule_coreflection`：invt
Submodule_reflection_of_invtSubmodule_coreflection (i : ι) (q : Submodule R N) (
hq : q in invtSubmodule (P.coreflection i)) : q.dualAnni…

--- 原说明 ---
When the coefficients are a field, the coroot conditions for irreducibility foll
ow from those
for the roots.
-/
lemma IsIrreducible.mk' {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M]
    (P : RootPairing ι K M N)
    (h : ∀ (q : Submodule K M), (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤) :
    P.IsIrreducible where
  nontrivial := inferInstance
  nontrivial' := (Module.nontrivial_dual_iff K).mp P.toPerfPair.symm.nontrivial
  eq_top_of_invtSubmodule_reflection := h
  eq_top_of_invtSubmodule_coreflection q stab ne_bot := by
    specialize h (q.dualAnnihilator.map P.toPerfPair.symm)
      fun i ↦ invtSubmodule_reflection_of_invtSubmodule_coreflection P i q (stab i)
    rw [Submodule.map_eq_top_iff, not_imp_comm] at h
    replace ne_bot : q.dualAnnihilator ≠ ⊤ := by simpa
    simpa using h ne_bot
/-
**RootPairing.isIrreducible_iff_invtRootSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：isIrreducible_iff_invtRootSubmodule {K : Type*} [Field K] [Module K M] [Mo
dule K N] [Nontrivial M] (P : RootPairing ι K M N) : P.IsIrreducible ↔ IsSimpleO
rder P.invtRootSubmodule
参数：P : RootPairing ι K M N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.instNontrivialSubtypeSubmoduleMemSublatticeInvtRootSubmodule
`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing
 R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection`：∀ {ι : Typ
e u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 
: AddCommGroup M}   {inst_2 : _root_.Module R M} {…
· 使用引理 `RootPairing.mem_invtRootSubmodule_iff`：mem_invtRootSubmodule_iff {q : Su
bmodule R M} : q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodul
e (P.reflection i)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `RootPairing.IsIrreducible.mk'`：∀ {ι : Type u_1} {M : Type u_3} {N : Type
 u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] {K : Type u_5}   [inst_2
 : Field K] [inst_3…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsSimpleOrder.eq_top_of_lt`：eq_top_of_lt : b = ⊤
-/
lemma isIrreducible_iff_invtRootSubmodule
    {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M] (P : RootPairing ι K M N) :
    P.IsIrreducible ↔ IsSimpleOrder P.invtRootSubmodule := by
  refine ⟨fun h ↦ ⟨fun ⟨q, hq⟩ ↦ ?_⟩, fun h ↦ IsIrreducible.mk' P fun q hq hq' ↦ ?_⟩
  · simp only [invtRootSubmodule.bot_mem, invtRootSubmodule.top_mem, Subtype.mk_eq_bot_iff,
      Subtype.mk_eq_top_iff]
    rw [mem_invtRootSubmodule_iff] at hq
    have := IsIrreducible.eq_top_of_invtSubmodule_reflection q hq
    tauto
  · let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
    replace hq' : ⊥ < q' := by simpa [q', bot_lt_iff_ne_bot, -IsSimpleOrder.bot_lt_iff_eq_top]
    suffices q' = ⊤ by simpa [q'] using this
    exact IsSimpleOrder.eq_top_of_lt hq'
/-
**RootPairing.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule** 
是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [NeZero 2] [
IsDomain R] [Module.IsTorsionFree R M] (q : Submodule R M),   (∀ (i : ι), q ∈ Mo
dule.End.invtSubmodule ↑(P.reflection i)) →     ∃ Φ, (∀ i ∈ Φ, ¬Disjoint q (R ∙ 
P.root i)) ∧ ∀ i ∉ Φ, q ≤ LinearMap.ker (P.coroot' i)
参数：P : RootPairing ι R M N；q : Submodule R M；∀ (i : ι), q ∈ Module.End.invtSubmo
dule ↑(P.reflection i)；∀ i ∈ Φ, ¬Disjoint q (R ∙ P.root i)；P.coroot' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_invtSubmodule_reflection_iff`：∀ {R : Type u_1} {M : Type u
_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {
x : M}   {f : Module.Dual R M} […
-/
lemma exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule
    [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] (q : Submodule R M)
    (hq : ∀ i, q ∈ invtSubmodule (P.reflection i)) :
    ∃ Φ : Set ι, (∀ i ∈ Φ, ¬ Disjoint q (R ∙ P.root i)) ∧ (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) := by
  refine ⟨{i | ¬ Disjoint q (R ∙ P.root i)}, by simp, fun i hi ↦ ?_⟩
  simp only [mem_ofPred_eq, not_not] at hi
  rw [← Submodule.mem_invtSubmodule_reflection_iff (by simp) hi]
  exact hq i

variable [NeZero (2 : R)] [P.IsIrreducible]
/-
**RootPairing.span_orbit_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：span_orbit_eq_top (i : ι) : span R (orbit P.weylGroup (P.root i)) = ⊤
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection`：∀ {ι : Typ
e u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 
: AddCommGroup M}   {inst_2 : _root_.Module R M} {…
· 使用引理 `RootPairing.reflection_mem_weylGroup`：reflection_mem_weylGroup : Equiv.r
eflection P i in P.weylGroup
· 使用引理 `Module.End.span_orbit_mem_invtSubmodule`：span_orbit_mem_invtSubmodule {G
 : Type*} [Monoid G] [DistribMulAction G M] [SMulCommClass G R M] (x : M) (g : G
) : span R (MulAction.orbit G…
· 使用定理 `RootPairing.Equiv.instSMulCommClassAut`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma span_orbit_eq_top (i : ι) :
    span R (orbit P.weylGroup (P.root i)) = ⊤ := by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j ↦ ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, mem_orbit_self _, P.ne_zero i⟩
/-
**RootPairing.exists_form_eq_form_and_form_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：exists_form_eq_form_and_form_ne_zero (B : P.InvariantForm) (i j : ι) : exi
sts k, B.form (P.root k) (P.root k) = B.form (P.root j) (P.root j) ∧ B.form (P.r
oot i) (P.root k) != 0
参数：B : P.InvariantForm；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.weylGroup_apply_root`：weylGroup_apply_root (g : P.weylGroup)
 (i : ι) : g • P.root i = P.root (P.weylGroupToPerm g i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RootPairing.Equiv.indexHom_apply`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.root_indexEquiv_eq_smul`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]  
 [inst_2 : _root_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `RootPairing.InvariantForm.apply_weylGroup_smul`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 M]   [inst_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.InvariantForm.apply_root_ne_zero`：apply_root_ne_zero : B.for
m (P.root i) != 0
· 使用引理 `RootPairing.span_orbit_eq_top`：span_orbit_eq_top (i : ι) : span R (orbit
 P.weylGroup (P.root i)) = ⊤
-/
lemma exists_form_eq_form_and_form_ne_zero (B : P.InvariantForm) (i j : ι) :
    ∃ k, B.form (P.root k) (P.root k) = B.form (P.root j) (P.root j) ∧
         B.form (P.root i) (P.root k) ≠ 0 := by
  by_contra! contra
  suffices span R (orbit P.weylGroup (P.root j)) ≤ ker (B.form (P.root i)) from
    B.apply_root_ne_zero i <| by simpa [span_orbit_eq_top] using this
  refine span_le.mpr fun v hv ↦ ?_
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  simp only [P.weylGroup_apply_root, SetLike.mem_coe, LinearMap.mem_ker]
  apply contra
  simp [← Subgroup.smul_def g]
/-
**RootPairing.span_root_image_eq_top_of_forall_orthogonal** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing`。
形式化陈述：span_root_image_eq_top_of_forall_orthogonal (s : Set ι) (hne : s.Nonempty)
 (h : forall j, P.root j ∉ span R (P.root '' s) -> forall i in s, P.IsOrthogonal
 j i) : span R (P.root '' s) = ⊤
参数：s : Set ι；hne : s.Nonempty；h : forall j, P.root j ∉ span R (P.root '' s) -> f
orall i in s, P.IsOrthogonal j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.mem_invtSubmodule_reflection_of_mem`：∀ {R : Type u_1} {M : Typ
e u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M
] {x : M}   {f : Module.Dual R M} (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用引理 `RootPairing.isFixedPt_reflection_of_isOrthogonal`：isFixedPt_reflection_o
f_isOrthogonal {s : Set ι} (hj : forall i in s, P.IsOrthogonal j i) {x : M} (hx 
: x in span R (P.root '' s)) : IsFixed…
· 使用定理 `RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection`：∀ {ι : Typ
e u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 
: AddCommGroup M}   {inst_2 : _root_.Module R M} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma span_root_image_eq_top_of_forall_orthogonal (s : Set ι)
    (hne : s.Nonempty) (h : ∀ j, P.root j ∉ span R (P.root '' s) → ∀ i ∈ s, P.IsOrthogonal j i) :
    span R (P.root '' s) = ⊤ := by
  have hq (j : ι) : span R (P.root '' s) ∈ Module.End.invtSubmodule (P.reflection j) := by
    by_cases hj : P.root j ∈ span R (P.root '' s)
    · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ hj
    · refine (Module.End.mem_invtSubmodule _).mpr fun x hx ↦ ?_
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe,
        (isFixedPt_reflection_of_isOrthogonal (h _ hj) hx).eq]
  apply IsIrreducible.eq_top_of_invtSubmodule_reflection _ hq
  simpa using ⟨hne.choose, hne.choose_spec, P.ne_zero _⟩

/-
Note that this actually holds for `RootPairing` provided we:
* assume `RootPairing.IsBalanced`,
* replace the assumption `q ≠ ⊥` with `¬ Disjoint P.rootSpan q`,
* replace the conclusion `q = ⊤` with `P.rootSpan ≤ q`.
-/
/-
**RootPairing.eq_top_of_mem_invtSubmodule_of_forall_eq_univ** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：eq_top_of_mem_invtSubmodule_of_forall_eq_univ {K : Type*} [Field K] [NeZer
o (2 : K)] [Module K M] [Module K N] (P : RootPairing ι K M N) [P.IsRootSystem] 
(q : Submodule K M) (h₀ : q != ⊥) (h₁ : forall i, q in invtSubmodule (P.reflecti
on i)) (h₂ : forall Φ, Φ.Nonempty -> P.root '' Φ subseteq q -> (forall i ∉ Φ, q 
<= ker (P.coroot' i)) -> Φ = univ) : q = ⊤
参数：2 : K；P : RootPairing ι K M N；q : Submodule K M；h₀ : q != ⊥；h₁ : forall i, q 
in invtSubmodule (P.reflection i)；h₂ : forall Φ, Φ.Nonempty -> P.root '' Φ subse
teq q -> (forall i ∉ Φ, q <= ker (P.coroot' i)) -> Φ = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmod
ule`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommR
ing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'`：corootSp
an_dualAnnihilator_map_eq_iInf_ker_coroot' : (P.corootSpan R).dualAnnihilator.ma
p (P.toPerfPair.symm : Dual R N ->ₗ[R] M) = ⨅ i, (P.…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `RootPairing.IsRootSystem.span_coroot_eq_top`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Submodule.disjoint_span_singleton'`：disjoint_span_singleton' (hx : x != 
0) : Disjoint s (K ∙ x) ↔ x ∉ s
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…

--- 原说明 ---
Note that this actually holds for `RootPairing` provided we:
* assume `RootPairing.IsBalanced`,
* replace the assumption `q ≠ ⊥` with `¬ Disjoint P.rootSpan q`,
* replace the conclusion `q = ⊤` with `P.rootSpan ≤ q`.
-/
lemma eq_top_of_mem_invtSubmodule_of_forall_eq_univ
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N]
    (P : RootPairing ι K M N) [P.IsRootSystem]
    (q : Submodule K M)
    (h₀ : q ≠ ⊥)
    (h₁ : ∀ i, q ∈ invtSubmodule (P.reflection i))
    (h₂ : ∀ Φ, Φ.Nonempty → P.root '' Φ ⊆ q → (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) → Φ = univ) :
    q = ⊤ := by
  obtain ⟨Φ, b, c⟩ := P.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule q h₁
  rcases Φ.eq_empty_or_nonempty with rfl | hΦ
  · replace c : q ≤ ⨅ i, LinearMap.ker (P.coroot' i) := by simpa using! c
    simp [h₀, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] at c
  · replace b : P.root '' Φ ⊆ q := by
      simpa [Submodule.disjoint_span_singleton' (P.ne_zero _)] using! b
    simpa [h₂ Φ hΦ b c, ← span_le] using! b

end RootPairing

