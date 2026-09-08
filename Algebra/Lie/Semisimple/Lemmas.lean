/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Lemmas about semisimple Lie algebras

This file is a home for lemmas about semisimple and reductive Lie algebras.

## Main definitions / results:
* `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`: a finite-dimensional Lie
  algebra with an irreducible faithful finite-dimensional representation is reductive.
* `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful`: a finite-dimensional Lie
  algebra with an irreducible faithful finite-dimensional trace-free representation is semisimple.

## TODO

* Introduce a `Prop`-valued typeclass `LieModule.IsTracefree` stating
  `(toEnd R L M).range ≤ LieAlgebra.derivedSeries R (Module.End R M) 1`, prove
  `f ∈ LieAlgebra.derivedSeries k (Module.End k V) 1 ↔ LinearMap.trace k _ f = 0`, and restate
  `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` using `LieModule.IsTracefree`.

-/

public section

namespace LieAlgebra

open LieModule LieSubmodule Module Set

variable (k L M : Type*) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
  [IsIrreducible k L M] [IsFaithful k L M] [IsTriangularizable k L M]

/-
**LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful** 是 Mathlib 中的
一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：hasCentralRadical_and_of_isIrreducible_of_isFaithful : HasCentralRadical k
 L ∧ (forall x, x in center k L ↔ toEnd k L M x in k ∙ LinearMap.id)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.nontrivial_of_isIrreducible`：LieModule.nontrivial_of_isIrreduc
ible [LieModule.IsIrreducible R L M] : Nontrivial M where exists_pair_ne
· 使用定理 `LieModule.exists_nontrivial_weightSpace_of_isSolvable`：exists_nontrivial
_weightSpace_of_isSolvable [IsSolvable L] [LieModule.IsTriangularizable k L V] :
 exists χ : Module.Dual k L, Nontrivial (we…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieModule.instIsTriangularizableSubtypeMemLieIdeal`：∀ (R : Type u_2) (L 
: Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : Li
eAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `instIsLieTowerSubtypeMemLieIdeal_1`：∀ (R : Type u) (L : Type v) (M : Typ
e w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : LieRingModule L M] […
· 使用定理 `instIsLieTowerSubtypeMemLieIdeal`：∀ (R : Type u) (L : Type v) (M : Type 
w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 
: LieRingModule L M] […
· 使用引理 `LieSubmodule.eq_top_of_isIrreducible`：LieSubmodule.eq_top_of_isIrreducib
le [LieModule.IsIrreducible R L M] (N : LieSubmodule R L M) [Nontrivial N] : N =
 ⊤
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Algebra.Lie.LieTheorem.0.LieModule.weightSpaceOfIsLieTo
wer_aux`：∀ {R : Type u_1} {L : Type u_2} {A : Type u_3} {V : Type u_4} [inst : C
ommRing R] [IsPrincipalIdealRing R] [IsDomain R]   [CharZero R] [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.weightSpaceOfIsLieTower.eq_1`：∀ (R : Type u_1) {L : Type u_2} 
{A : Type u_3} (V : Type u_4) [inst : CommRing R] [inst_1 : IsPrincipalIdealRing
 R]   [inst_2 : IsDomain R] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieIdeal.coe_bracket_of_module`：LieIdeal.coe_bracket_of_module {R L : Ty
pe*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L) [LieRingModule
 L M] (x : I) (m : M…
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieModule.mem_maxTrivSubmodule`：mem_maxTrivSubmodule (m : M) : m in maxT
rivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `LieModule.toEnd_eq_zero_iff`：toEnd_eq_zero_iff [IsFaithful R L M] {x : L
} : toEnd R L M x = 0 ↔ x = 0
（共 39 条，此处仅展示前 30 条）
-/
lemma hasCentralRadical_and_of_isIrreducible_of_isFaithful :
    HasCentralRadical k L ∧ (∀ x, x ∈ center k L ↔ toEnd k L M x ∈ k ∙ LinearMap.id) := by
  have _i := nontrivial_of_isIrreducible k L M
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual k (radical k L), Nontrivial (weightSpace M χ) :=
    exists_nontrivial_weightSpace_of_isSolvable k (radical k L) M
  let N : LieSubmodule k L M := weightSpaceOfIsLieTower k M χ
  replace hχ : Nontrivial N := hχ
  replace hχ : N = ⊤ := N.eq_top_of_isIrreducible k L M
  replace hχ (x : L) (hx : x ∈ radical k L) : toEnd k _ M x = χ ⟨x, hx⟩ • LinearMap.id := by
    ext m
    have hm : ∀ (y : L) (hy : y ∈ radical k L), ⁅y, m⁆ = χ ⟨y, hy⟩ • m := by
      simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using (hχ ▸ mem_top _ : m ∈ N)
    simpa using hm x hx
  have aux : radical k L = center k L := by
    refine le_antisymm (fun x hx ↦ (mem_maxTrivSubmodule k L L x).mpr ?_) (center_le_radical k L)
    intro y
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, hχ _ hx, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]
  refine ⟨⟨aux⟩, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ (mem_maxTrivSubmodule k L L x).mpr fun y ↦ ?_⟩⟩
  · rw [← aux] at hx
    exact Submodule.mem_span_singleton.mpr ⟨χ ⟨x, hx⟩, (hχ x hx).symm⟩
  · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, ← ht, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]
/-
**LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful** 是 Mathlib 中的一个定理
，位于命名空间 `LieAlgebra`。
形式化陈述：hasTrivialRadical_of_isIrreducible_of_isFaithful (h : forall x, LinearMap.
trace k _ (toEnd k L M x) = 0) : HasTrivialRadical k L
参数：h : forall x, LinearMap.trace k _ (toEnd k L M x) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `LieModule.nontrivial_of_isIrreducible`：LieModule.nontrivial_of_isIrreduc
ible [LieModule.IsIrreducible R L M] : Nontrivial M where exists_pair_ne
· 使用引理 `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`：hasCent
ralRadical_and_of_isIrreducible_of_isFaithful : HasCentralRadical k L ∧ (forall 
x, x in center k L ↔ toEnd k L M x in k ∙ LinearMap.i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.hasTrivialRadical_iff`：∀ (R : Type u_1) (L : Type u_2) [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   LieAlgebra.HasTr
ivialRadical R L ↔ Lie…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieAlgebra.hasCentralRadical_iff`：∀ (R : Type u_1) (L : Type u_2) [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   LieAlgebra.HasCe
ntralRadical R L ↔ Lie…
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.trace_id`：trace_id : trace R M id = (finrank R M : R)
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 33 条，此处仅展示前 30 条）
-/
theorem hasTrivialRadical_of_isIrreducible_of_isFaithful
    (h : ∀ x, LinearMap.trace k _ (toEnd k L M x) = 0) : HasTrivialRadical k L := by
  have : finrank k M ≠ 0 := (finrank_pos_iff.mpr <| nontrivial_of_isIrreducible k L M).ne'
  obtain ⟨_i, h'⟩ := hasCentralRadical_and_of_isIrreducible_of_isFaithful k L M
  rw [hasTrivialRadical_iff, (hasCentralRadical_iff k L).mp inferInstance, LieSubmodule.eq_bot_iff]
  intro x hx
  specialize h x
  rw [h' x] at hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
  suffices t = 0 by simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), ← ht, this]
  simpa [this, ← ht] using h

variable {k L M}
variable {R : Type*} [CommRing R] [LieAlgebra R L] [Module R M] [LieModule R L M]

open LinearMap in
/-
**LieAlgebra.trace_toEnd_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：trace_toEnd_eq_zero {s : Set L} (hs : forall x in s, LinearMap.trace R _ (
toEnd R _ M x) = 0) {x : L} (hx : x in LieSubalgebra.lieSpan R L s) : trace R _ 
(toEnd R _ M x) = 0
参数：hs : forall x in s, LinearMap.trace R _ (toEnd R _ M x) = 0；hx : x in LieSuba
lgebra.lieSpan R L s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用引理 `LinearMap.trace_lie`：trace_lie {R M : Type*} [CommRing R] [AddCommGroup 
M] [Module R M] (f g : Module.End R M) : trace R M ⁅f, g⁆ = 0
-/
lemma trace_toEnd_eq_zero {s : Set L} (hs : ∀ x ∈ s, LinearMap.trace R _ (toEnd R _ M x) = 0)
    {x : L} (hx : x ∈ LieSubalgebra.lieSpan R L s) :
    trace R _ (toEnd R _ M x) = 0 := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu => simpa using hs u hu
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]
  | lie u v _ _ _ _ => simp

end LieAlgebra

