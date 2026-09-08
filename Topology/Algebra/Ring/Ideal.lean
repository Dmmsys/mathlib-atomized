/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Ideals and quotients of topological rings

In this file we define `Ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `TopologicalSpace` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/

@[expose] public section

open Topology

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

/-- The closure of an ideal in a topological ring as an ideal. -/
/-
**Ideal.closure** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} → [inst : TopologicalSpace R] → [inst_1 : Ring R] → [IsTopo
logicalRing R] → Ideal R → Ideal R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of an ideal in a topological ring as an ideal.
-/
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }

@[simp]
/-
**Ideal.coe_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I :=
  rfl

/--
This is not `@[simp]` since otherwise it causes timeouts downstream as `simp` tries and fails to
generate an `IsClosed` instance.
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234852.20heartbeats.20of.20the.20linter
-/
/-
**Ideal.closure_eq_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.closure_eq_of_isClosed (I : Ideal R) (hI : IsClosed (I : Set R)) : I
.closure = I
参数：I : Ideal R；hI : IsClosed (I : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
This is not `@[simp]` since otherwise it causes timeouts downstream as `simp` tr
ies and fails to
generate an `IsClosed` instance.
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234852.
20heartbeats.20of.20the.20linter
-/
theorem Ideal.closure_eq_of_isClosed (I : Ideal R) (hI : IsClosed (I : Set R)) : I.closure = I :=
  SetLike.ext' hI.closure_eq

variable (R)

/-- The connected component of zero in a topological ring as an ideal. -/
/-
**Ideal.connectedComponentOfZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.connectedComponentOfZero : Ideal R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected component of zero in a topological ring as an ideal.
-/
def Ideal.connectedComponentOfZero : Ideal R where
  __ := AddSubgroup.connectedComponentOfZero R
  smul_mem' c x h := IsConnected.subset_connectedComponent
    (isConnected_connectedComponent.image _ (continuous_const_mul c).continuousOn)
    ⟨0, mem_connectedComponent, mul_zero c⟩ ⟨x, h, rfl⟩

@[simp]
/-
**Ideal.coe_connectedComponentOfZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.coe_connectedComponentOfZero : (Ideal.connectedComponentOfZero R : S
et R) = connectedComponent 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ideal.coe_connectedComponentOfZero :
    (Ideal.connectedComponentOfZero R : Set R) = connectedComponent 0 :=
  rfl

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] (N : Ideal R)

open Ideal.Quotient

/-
**topologicalRingQuotientTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N) :=
  instTopologicalSpaceQuotient

-- note for the reader: in the following, `mk` is `Ideal.Quotient.mk`, the canonical map `R → R/I`.
variable [IsTopologicalRing R]
/-
**QuotientRing.isOpenMap_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientRing.isOpenMap_coe : IsOpenMap (mk N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.isOpenMap_coe`：∀ {G : Type u_1} [inst : TopologicalSpac
e G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] {N : AddSubgroup G},   Is
OpenMap QuotientAddG…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem QuotientRing.isOpenMap_coe : IsOpenMap (mk N) :=
  QuotientAddGroup.isOpenMap_coe
/-
**QuotientRing.isOpenQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientRing.isOpenQuotientMap_mk : IsOpenQuotientMap (mk N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.isOpenQuotientMap_mk`：∀ {G : Type u_1} [inst : Topologi
calSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] {N : AddSubgroup G
},   IsOpenQuotientMap Quot…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem QuotientRing.isOpenQuotientMap_mk : IsOpenQuotientMap (mk N) :=
  QuotientAddGroup.isOpenQuotientMap_mk
/-
**QuotientRing.isQuotientMap_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientRing.isQuotientMap_coe_coe : IsQuotientMap fun p : R × R => (mk N 
p.1, mk N p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `QuotientRing.isOpenQuotientMap_mk`：QuotientRing.isOpenQuotientMap_mk : I
sOpenQuotientMap (mk N)
-/
theorem QuotientRing.isQuotientMap_coe_coe : IsQuotientMap fun p : R × R => (mk N p.1, mk N p.2) :=
  ((isOpenQuotientMap_mk N).prodMap (isOpenQuotientMap_mk N)).isQuotientMap
/-
**topologicalRing_quotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：topologicalRing_quotient : IsTopologicalRing (R ⧸ N) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.instIsTopologicalAddGroup`：∀ {G : Type u_1} [inst : Top
ologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (N : AddSubgrou
p G)   [inst_3 : N.Normal], IsTo…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `QuotientRing.isQuotientMap_coe_coe`：QuotientRing.isQuotientMap_coe_coe :
 IsQuotientMap fun p : R × R => (mk N p.1, mk N p.2)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance topologicalRing_quotient : IsTopologicalRing (R ⧸ N) where
  __ := QuotientAddGroup.instIsTopologicalAddGroup _
  continuous_mul := (QuotientRing.isQuotientMap_coe_coe N).continuous_iff.2 <|
    continuous_quot_mk.comp continuous_mul
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace R] : CompactSpace (R ⧸ N) :=
  Quotient.compactSpace

end CommRing

