/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm

/-!
# Lie algebras with non-degenerate Killing forms.

In characteristic zero, the following three conditions are equivalent:
1. The solvable radical of a Lie algebra is trivial
2. A Lie algebra is a direct sum of its simple ideals
3. A Lie algebra has non-degenerate Killing form

In positive characteristic, it is still true that 3 implies 2, and that 2 implies 1, but there are
counterexamples to the remaining implications. Thus condition 3 is the strongest assumption.
Furthermore, much of the Cartan-Killing classification of semisimple Lie algebras in characteristic
zero, continues to hold in positive characteristic (over a perfect field) if the Lie algebra has a
non-degenerate Killing form.

This file contains basic definitions and results for such Lie algebras.

## Main declarations

* `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
  Killing form.
* `LieAlgebra.IsKilling.instSemisimple`: if a finite-dimensional Lie algebra over a field
  has non-singular Killing form then it is semisimple.
* `LieAlgebra.IsKilling.instHasTrivialRadical`: if a Lie algebra over a PID
  has non-singular Killing form then it has trivial radical.
* `LieIdeal.isCompl_killingCompl`: if a Lie algebra has non-singular Killing form then for all
  ideals, an ideal and its Killing orthogonal complement are complements.

-/

public section

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
/-
**LieAlgebra.IsKilling** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) → (L : Type u_3) → [inst : CommRing R] → [inst_1 : LieRing 
L] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie a
lgebras with this
property).
-/
class IsKilling : Prop where
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]

/-
**LieAlgebra.IsKilling.ker_killingForm_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra.IsKilling`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   [LieAlgebra.IsKilling R L], LinearMap.ker (killingFor
m R L) = ⊥
参数：R : Type u_1；L : Type u_3；killingForm R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.IsKilling.killingCompl_top_eq_bot`：∀ {R : Type u_1} {L : Type
 u_3} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self
 : LieAlgebra.IsKilling R L], LieI…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]
/-
**LieAlgebra.IsKilling.killingForm_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra.IsKilling`。
形式化陈述：killingForm_nondegenerate : (killingForm R L).Nondegenerate
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

variable {R L} in
/-
**LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：ideal_eq_bot_of_isLieAbelian [Module.Free R L] [Module.Finite R L] [IsDoma
in R] [IsPrincipalIdealRing R] (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.IsKilling.killingCompl_top_eq_bot`：∀ {R : Type u_1} {L : Type
 u_3} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self
 : LieAlgebra.IsKilling R L], LieI…
· 使用定理 `LieIdeal.le_killingCompl_top_of_isLieAbelian`：∀ (R : Type u_1) (L : Type
 u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : Li
eIdeal R L)   [Module.Free R L] [M…
-/
lemma ideal_eq_bot_of_isLieAbelian
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
    (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian
/-
**LieAlgebra.IsKilling.instSemisimple** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsKi
lling`。
形式化陈述：instSemisimple [IsKilling K L] [Module.Finite K L] : IsSemisimple K L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate`：isSemisimple_of_
nondegenerate : IsSemisimple K L
· 使用引理 `LieAlgebra.IsKilling.killingForm_nondegenerate`：killingForm_nondegenerat
e : (killingForm R L).Nondegenerate
· 使用引理 `LieModule.traceForm_lieInvariant`：traceForm_lieInvariant : (traceForm R 
L M).lieInvariant L
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian`：ideal_eq_bot_of_isLie
Abelian [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing
 R] (I : LieIdeal R L) [IsLieAbelian I]…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
instance instSemisimple [IsKilling K L] [Module.Finite K L] : IsSemisimple K L := by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
    exact h₁.1 <| IsKilling.ideal_eq_bot_of_isLieAbelian I

/-- The converse of this is true in characteristic zero; it is
`LieAlgebra.HasTrivialRadical.instIsKilling`. There are counterexamples
over fields with positive characteristic.

Note that when the coefficients are a field this instance is redundant since we have
`LieAlgebra.IsKilling.instSemisimple` and `LieAlgebra.IsSemisimple.instHasTrivialRadical`. -/
/-
**LieAlgebra.IsKilling.instHasTrivialRadical** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgeb
ra.IsKilling`。
形式化陈述：instHasTrivialRadical [Module.Free R L] [Module.Finite R L] [IsDomain R] [
IsPrincipalIdealRing R] : HasTrivialRadical R L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`：hasTrivialRadical_if
f_no_abelian_ideals : HasTrivialRadical R L ↔ forall I : LieIdeal R L, IsLieAbel
ian I -> I = ⊥
· 使用引理 `LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian`：ideal_eq_bot_of_isLie
Abelian [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing
 R] (I : LieIdeal R L) [IsLieAbelian I]…

--- 原说明 ---
The converse of this is true in characteristic zero; it is
`LieAlgebra.HasTrivialRadical.instIsKilling`. There are counterexamples
over fields with positive characteristic.

Note that when the coefficients are a field this instance is redundant since we 
have
`LieAlgebra.IsKilling.instSemisimple` and `LieAlgebra.IsSemisimple.instHasTrivia
lRadical`.
-/
instance instHasTrivialRadical
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    HasTrivialRadical R L :=
  (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian
/-
**LieAlgebra.IsKilling.isLieAbelian_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra.IsKilling`。
形式化陈述：isLieAbelian_iff_subsingleton [Module.Free R L] [Module.Finite R L] [IsDom
ain R] [IsPrincipalIdealRing R] : IsLieAbelian L ↔ Subsingleton L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.center_eq_bot`：center_eq_bot [LieModule.IsFaithful R L L] : c
enter R L = ⊥
· 使用定理 `LieAlgebra.instIsFaithfulOfHasTrivialRadical`：∀ (R : Type u_1) (L : Type
 u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieA
lgebra.HasTrivialRadical R L], Lie…
· 使用定理 `LieAlgebra.isLieAbelian_iff_center_eq_top`：isLieAbelian_iff_center_eq_to
p : IsLieAbelian L ↔ center R L = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.subsingleton_iff`：subsingleton_iff : Subsingleton (LieSubmo
dule R L M) ↔ Subsingleton M
· 使用定理 `subsingleton_of_top_eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst
_1 : BoundedOrder α], ⊤ = ⊥ → Subsingleton α
-/
theorem isLieAbelian_iff_subsingleton
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    IsLieAbelian L ↔ Subsingleton L := by
  constructor
  · intro h
    rw [isLieAbelian_iff_center_eq_top R] at h
    have hc : (⊤ : LieIdeal R L) = ⊥ := by rw [← center_eq_bot R L, h]
    exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_top_eq_bot hc)
  · exact fun _ => inferInstance

end IsKilling

section LieEquiv

variable {R L}
variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and elements `x y : L`, the
respective Killing forms of `L` and `L'` satisfy `κ'(e x, e y) = κ(x, y)`. -/
/-
**LieAlgebra.killingForm_of_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {L' : Type u_4}   [inst_3 : LieRing L'] [inst_4 : LieAl
gebra R L'] (e : L ≃ₗ⁅R⁆ L') (x y : L),   ((killingForm R L') (e x)) (e y) = ((k
illingForm R L) x) y
参数：e : L ≃ₗ⁅R⁆ L'；x y : L；(killingForm R L') (e x)；e y；(killingForm R L) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `killingForm_apply_apply`：killingForm_apply_apply (x y : L) : killingForm
 R L x y = trace R L (ad R L x ∘ₗ ad R L y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an equivalence `e` of Lie algebras from `L` to `L'`, and elements `x y : L
`, the
respective Killing forms of `L` and `L'` satisfy `κ'(e x, e y) = κ(x, y)`.
-/
@[simp] lemma killingForm_of_equiv_apply (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    killingForm R L' (e x) (e y) = killingForm R L x y := by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']

/-- Given a Killing Lie algebra `L`, if `L'` is isomorphic to `L`, then `L'` is Killing too. -/
/-
**LieAlgebra.isKilling_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L'
参数：e : L ≃ₗ⁅R⁆ L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LieAlgebra.killingForm_of_equiv_apply`：∀ {R : Type u_1} {L : Type u_3} [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {L' : Type u_4
}   [inst_3 : LieRing L'] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieEquiv.apply_symm_apply`：apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x
, e (e.symm x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.congr_arg`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用定理 `LinearMap.map_zero₂`：map_zero₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y) : f 0
 y = 0

--- 原说明 ---
Given a Killing Lie algebra `L`, if `L'` is isomorphic to `L`, then `L'` is Kill
ing too.
-/
lemma isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L' := by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' ↦ ?_, fun hx y _ ↦ hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' ∈ LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa [map_zero] using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : ∀ y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'

alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv

end LieEquiv

end LieAlgebra

open LieAlgebra in
variable {K L} in
/-
**LieIdeal.isCompl_killingCompl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieIdeal.isCompl_killingCompl [IsKilling K L] [Module.Finite K L] (I : Lie
Ideal K L) : IsCompl I I.killingCompl
参数：I : LieIdeal K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.traceForm_apply_lie_apply`：traceForm_apply_lie_apply (x y z : 
L) : traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieIdeal.mem_killingCompl`：∀ (R : Type u_1) (L : Type u_3) [inst : CommR
ing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : LieIdeal R L)   {x : 
L}, x ∈ LieIdea…
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用定理 `LieSubmodule.lie_abelian_iff_lie_self_eq_bot`：LieSubmodule.lie_abelian_i
ff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
· 使用定理 `LieSubmodule.lie_eq_bot_iff`：lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ forall x in I
, forall m in N, ⁅(x : L), m⁆ = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `LieAlgebra.IsKilling.killingForm_nondegenerate`：killingForm_nondegenerat
e : (killingForm R L).Nondegenerate
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用引理 `LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian`：ideal_eq_bot_of_isLie
Abelian [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing
 R] (I : LieIdeal R L) [IsLieAbelian I]…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.isCompl_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type 
w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 
: _root_.Module R M] […
· 使用定理 `LieIdeal.toSubmodule_killingCompl`：∀ (R : Type u_1) (L : Type u_3) [inst
 : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : LieIdeal R L)
,   ↑(LieIdeal.killingC…
· 使用引理 `LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint`：isCompl_orthogonal_
iff_disjoint (hB₀ : B.IsRefl) : IsCompl W (B.orthogonal W) ↔ Disjoint W (B.ortho
gonal W)
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用定理 `LieSubmodule.disjoint_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
lemma LieIdeal.isCompl_killingCompl [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices IsLieAbelian (I ⊓ I.killingCompl : LieIdeal K L) by
    rw [disjoint_iff]
    exact IsKilling.ideal_eq_bot_of_isLieAbelian _
  suffices ∀ (x y z : L) (hx : x ∈ killingCompl K L I) (hy : y ∈ I),
      LieModule.traceForm K L L ⁅x, y⁆ z = 0 by
    rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot, LieSubmodule.lie_eq_bot_iff]
    rintro x ⟨-, hx⟩ y ⟨hy, -⟩
    exact (IsKilling.killingForm_nondegenerate K L).1 _ fun z ↦ this x y z hx hy
  intro x y z hx hy
  rw [LieModule.traceForm_apply_lie_apply K L L x y z, LieModule.traceForm_comm K L L]
  exact I.mem_killingCompl.mp hx _ <| lie_mem_left K L I y z hy
