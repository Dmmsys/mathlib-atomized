/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Data.ENat.Lattice

/-! # Substitutions in multivariate power series

Here we define the substitution of power series into other power series.
We follow [Bourbaki, Algebra II, chap. 4, §4, n° 3][bourbaki1981]
who present substitution of power series as an application of evaluation.

For an `R`-algebra `S`, `f : MvPowerSeries σ R` and `a : σ → MvPowerSeries τ S`,
`MvPowerSeries.subst a f` is the substitution of `X s` by `a s` in `f`.
It is only well defined under one of the two following conditions:
  * `f` is a polynomial, in which case it is the classical evaluation;
  * or the condition `MvPowerSeries.HasSubst a` holds, which means:
    - For every `s`, the constant coefficient of `a s` is nilpotent;
    - For every `d : σ →₀ ℕ`, all but finitely many of the coefficients
      `(a s).coeff d` vanish.

In the other cases, it is defined as 0 (dummy value).

When `HasSubst a`, `MvPowerSeries.subst a` gives rise to an algebra homomorphism
`MvPowerSeries.substAlgHom ha : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S`.

We also define `MvPowerSeries.rescale` which rescales a multivariate
power series `f : MvPowerSeries σ R` by a map `a : σ → R`
and show its relation with substitution (under `CommRing R`).
To stay in line with `PowerSeries.rescale`, this is defined by hand
for commutative *semirings*.

## Implementation note

Evaluation of a power series at adequate elements has been defined
in `Mathlib/RingTheory/MvPowerSeries/Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having nilpotent constant coefficient
* Multivariate power series have a linear topology

The function `MvPowerSeries.subst` is defined using an explicit
invocation of the discrete uniformity (`⊥`).
If users need to enter the API, they can use `MvPowerSeries.subst_eq_eval₂`
and similar lemmas that hold for whatever uniformity on the space as soon
as it is discrete.

## TODO

* `MvPowerSeries.IsNilpotent_subst` asserts that the constant coefficient
  of a legit substitution is nilpotent; prove that the converse holds when
  the kernel of `algebraMap R S` is a nil ideal.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ : Type*}
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

attribute [local instance] DiscreteTopology.instContinuousSMul

/-- Families of power series which can be substituted -/
@[mk_iff hasSubst_def]
/-
**MvPowerSeries.HasSubst** 是 Mathlib 中的一个归纳类型，位于命名空间 `MvPowerSeries`。
形式化陈述：{σ : Type u_1} → {τ : Type u_4} → {S : Type u_5} → [CommRing S] → (σ → MvP
owerSeries τ S) → Prop
参数：σ → MvPowerSeries τ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Families of power series which can be substituted
-/
structure HasSubst (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff s : IsNilpotent (constantCoeff (a s))
  coeff_zero d : {s | (a s).coeff d ≠ 0}.Finite

variable {a : σ → MvPowerSeries τ S}
/-
**MvPowerSeries.coeff_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_iff [TopologicalSpace S] [DiscreteTopology S] : Filter.Tendsto 
a Filter.cofinite (nhds 0) ↔ forall d : τ ->₀ Nat, {s | (a s).coeff d != 0}.Fini
te
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coeff_zero_iff [TopologicalSpace S] [DiscreteTopology S] :
    Filter.Tendsto a Filter.cofinite (nhds 0) ↔
      ∀ d : τ →₀ ℕ, {s | (a s).coeff d ≠ 0}.Finite := by
  simp [tendsto_iff_coeff_tendsto, coeff_zero, nhds_discrete]

/-- A multivariate power series can be substituted if and only if
it can be evaluated when the topology on the coefficients ring is the discrete topology. -/
/-
**MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology** 是 Mathlib 中的一个引理，位于命名
空间 `MvPowerSeries`。
形式化陈述：hasSubst_iff_hasEval_of_discreteTopology [TopologicalSpace S] [DiscreteTop
ology S] : HasSubst a ↔ HasEval a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A multivariate power series can be substituted if and only if
it can be evaluated when the topology on the coefficients ring is the discrete t
opology.
-/
lemma hasSubst_iff_hasEval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] :
    HasSubst a ↔ HasEval a := by
  simp_rw [hasSubst_def, hasEval_def, coeff_zero_iff,
    isTopologicallyNilpotent_iff_constantCoeff_isNilpotent]
/-
**MvPowerSeries.HasSubst.hasEval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSub
st`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] {a : σ 
→ MvPowerSeries τ S}   [inst_1 : TopologicalSpace S], MvPowerSeries.HasSubst a →
 MvPowerSeries.HasEval a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.mono`：∀ {σ : Type u_1} {S : Type u_4} [inst : Comm
Ring S] {a : σ → S} {t u : TopologicalSpace S},   t ≤ u → MvPowerSeries.HasEval 
a → MvPowerSerie…
· 使用定理 `MvPowerSeries.WithPiTopology.instTopologicalSpace_mono`：instTopologicalS
pace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t <= u) : @i
nstTopologicalSpace σ R t <= @instTopologica…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`：hasSubst_iff_has
Eval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] : HasSubst a 
↔ HasEval a
-/
theorem HasSubst.hasEval [TopologicalSpace S] (ha : HasSubst a) :
    HasEval a := HasEval.mono (instTopologicalSpace_mono τ bot_le) <|
  (@hasSubst_iff_hasEval_of_discreteTopology σ τ _ _ a ⊥ (@DiscreteTopology.mk S ⊥ rfl)).mp ha
/-
**MvPowerSeries.HasSubst.zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`
。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S], MvPowe
rSeries.HasSubst fun x => 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `MvPowerSeries.HasEval.zero`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S], MvPowerSeries.HasEval 0
-/
theorem HasSubst.zero : HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) := by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using! HasEval.zero
/-
**MvPowerSeries.HasSubst.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] {a b : 
σ → MvPowerSeries τ S},   MvPowerSeries.HasSubst a → MvPowerSeries.HasSubst b → 
MvPowerSeries.HasSubst (a + b)
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`：hasSubst_iff_has
Eval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] : HasSubst a 
↔ HasEval a
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `MvPowerSeries.HasEval.add`：∀ {σ : Type u_1} {S : Type u_3} [inst : CommR
ing S] [inst_1 : TopologicalSpace S] [ContinuousAdd S]   [IsLinearTopology S S] 
{a b : σ → S}, …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
-/
theorem HasSubst.add {a b : σ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) := by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact ha.add hb
/-
**MvPowerSeries.HasSubst.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSu
bst`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] (b : σ 
→ MvPowerSeries τ S)   {a : σ → MvPowerSeries τ S}, MvPowerSeries.HasSubst a → M
vPowerSeries.HasSubst (b * a)
参数：b : σ → MvPowerSeries τ S；b * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`：hasSubst_iff_has
Eval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] : HasSubst a 
↔ HasEval a
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `MvPowerSeries.HasEval.mul_left`：∀ {σ : Type u_1} {S : Type u_3} [inst : 
CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   {
x : σ → S}, MvPowerS…
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
-/
theorem HasSubst.mul_left (b : σ → MvPowerSeries τ S)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (b * a) := by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact ha.mul_left b
/-
**MvPowerSeries.HasSubst.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasS
ubst`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] (b : σ 
→ MvPowerSeries τ S)   {a : σ → MvPowerSeries τ S}, MvPowerSeries.HasSubst a → M
vPowerSeries.HasSubst (a * b)
参数：b : σ → MvPowerSeries τ S；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.mul_left`：∀ {σ : Type u_1} {τ : Type u_4} {S : Ty
pe u_5} [inst : CommRing S] (b : σ → MvPowerSeries τ S)   {a : σ → MvPowerSeries
 τ S}, MvPowerSeries.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem HasSubst.mul_right (b : σ → MvPowerSeries τ S)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (a * b) :=
  mul_comm a b ▸ ha.mul_left b
/-
**MvPowerSeries.HasSubst.smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`
。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] (r : Mv
PowerSeries τ S) {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasSubst a → MvPow
erSeries.HasSubst (r • a)
参数：r : MvPowerSeries τ S；r • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.mul_left`：∀ {σ : Type u_1} {τ : Type u_4} {S : Ty
pe u_5} [inst : CommRing S] (b : σ → MvPowerSeries τ S)   {a : σ → MvPowerSeries
 τ S}, MvPowerSeries.…
-/
theorem HasSubst.smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := ha.mul_left _
/-
**MvPowerSeries.HasSubst.X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRing S], MvPowerSeries.HasSubs
t fun s => MvPowerSeries.X s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `MvPowerSeries.HasEval.X`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRin
g R] [inst_1 : TopologicalSpace R],   MvPowerSeries.HasEval fun s => MvPowerSeri
es.X s
-/
protected theorem HasSubst.X : HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) := by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.X

omit [Algebra R S] in
/-
**MvPowerSeries.HasSubst.map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {τ : Type u_4} {S : Ty
pe u_5} [inst_1 : CommRing S]   {a : σ → MvPowerSeries τ R},   MvPowerSeries.Has
Subst a → ∀ (h : R →+* S), MvPowerSeries.HasSubst fun i => (MvPowerSeries.map h)
 (a i)
参数：h : R →+* S；MvPowerSeries.map h；a i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.HasSubst.const_coeff`：∀ {σ : Type u_1} {τ : Type u_4} {S :
 Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasS
ubst a → ∀ (s : σ), IsNi…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `MvPowerSeries.HasSubst.coeff_zero`：∀ {σ : Type u_1} {τ : Type u_4} {S : 
Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasSu
bst a → ∀ (d : τ →₀ ℕ),…
-/
protected theorem HasSubst.map {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (h : R →+* S) :
    HasSubst fun i ↦ (map h) (a i) where
  const_coeff s := (ha.const_coeff s).map h
  coeff_zero d := (ha.coeff_zero d).subset (by grind [coeff_map])
/-
**MvPowerSeries.HasSubst.smul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubs
t`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] (a : σ → R), MvPowerSe
ries.HasSubst (a • MvPowerSeries.X)
参数：a : σ → R；a • MvPowerSeries.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebra_compatible_smul`：algebra_compatible_smul (r : R) (m : M) : r • m
 = (algebraMap R A) r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MvPowerSeries.HasSubst.mul_left`：∀ {σ : Type u_1} {τ : Type u_4} {S : Ty
pe u_5} [inst : CommRing S] (b : σ → MvPowerSeries τ S)   {a : σ → MvPowerSeries
 τ S}, MvPowerSeries.…
· 使用定理 `MvPowerSeries.HasSubst.X`：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRi
ng S], MvPowerSeries.HasSubst fun s => MvPowerSeries.X s
-/
theorem HasSubst.smul_X (a : σ → R) :
    HasSubst (a • X : σ → MvPowerSeries σ R) := by
  convert! HasSubst.X.mul_left (fun s ↦ algebraMap R (MvPowerSeries σ R) (a s))
  simp [funext_iff, algebra_compatible_smul (MvPowerSeries σ R)]

/-- Families of `MvPowerSeries` that can be substituted, as an `Ideal` -/
/-
**MvPowerSeries.hasSubstIdeal** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：hasSubstIdeal : Ideal (σ -> MvPowerSeries τ S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.add`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_
5} [inst : CommRing S] {a b : σ → MvPowerSeries τ S},   MvPowerSeries.HasSubst a
 → MvPowerSeries…
· 使用定理 `MvPowerSeries.HasSubst.zero`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u
_5} [inst : CommRing S], MvPowerSeries.HasSubst fun x => 0
· 使用定理 `MvPowerSeries.HasSubst.mul_left`：∀ {σ : Type u_1} {τ : Type u_4} {S : Ty
pe u_5} [inst : CommRing S] (b : σ → MvPowerSeries τ S)   {a : σ → MvPowerSeries
 τ S}, MvPowerSeries.…

--- 原说明 ---
Families of `MvPowerSeries` that can be substituted, as an `Ideal`
-/
noncomputable def hasSubstIdeal : Ideal (σ → MvPowerSeries τ S) :=
  { carrier := Set.ofPred HasSubst
    add_mem' := HasSubst.add
    zero_mem' := HasSubst.zero
    smul_mem' := HasSubst.mul_left }

/-- If `σ` is finite, then the nilpotent condition is enough for `HasSubst` -/
/-
**MvPowerSeries.hasSubst_of_constantCoeff_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries`。
形式化陈述：hasSubst_of_constantCoeff_nilpotent [Finite σ] {a : σ -> MvPowerSeries τ S
} (ha : forall s, IsNilpotent (constantCoeff (a s))) : HasSubst a where const_co
eff
参数：ha : forall s, IsNilpotent (constantCoeff (a s))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
If `σ` is finite, then the nilpotent condition is enough for `HasSubst`
-/
theorem hasSubst_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff (a s))) :
    HasSubst a where
  const_coeff := ha
  coeff_zero _ := Set.toFinite _

/-- If `σ` is finite, then having zero constant coefficient is enough for `HasSubst` -/
/-
**MvPowerSeries.hasSubst_of_constantCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowe
rSeries`。
形式化陈述：hasSubst_of_constantCoeff_zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha
 : forall s, constantCoeff (a s) = 0) : HasSubst a
参数：ha : forall s, constantCoeff (a s) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent`：hasSubst_of_constantC
oeff_nilpotent [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, IsNilpote
nt (constantCoeff (a s))) : HasSubst a …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `σ` is finite, then having zero constant coefficient is enough for `HasSubst`
-/
theorem hasSubst_of_constantCoeff_zero [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  hasSubst_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])
/-
**MvPowerSeries.HasSubst.X_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {i j : σ},   MvPowerSe
ries.HasSubst ![MvPowerSeries.X i, MvPowerSeries.X j]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma HasSubst.X_X {i j : σ} : HasSubst (S := R) ![X i, X j] :=
  hasSubst_of_constantCoeff_zero (by simp)
/-
**MvPowerSeries.HasSubst.X_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubs
t`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {i : σ}, MvPowerSeries
.HasSubst ![MvPowerSeries.X i, 0]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma HasSubst.X_zero {i : σ} : HasSubst ![X i (R := R), 0] :=
  hasSubst_of_constantCoeff_zero (by simp)
/-
**MvPowerSeries.HasSubst.zero_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubs
t`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {i : σ}, MvPowerSeries
.HasSubst ![0, MvPowerSeries.X i]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma HasSubst.zero_X {i : σ} : HasSubst ![0, X i (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)
/-
**MvPowerSeries.HasSubst.pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] {n : ℕ}
,   n ≠ 0 → ∀ {a : σ → MvPowerSeries τ S}, MvPowerSeries.HasSubst a → MvPowerSer
ies.HasSubst (a ^ n)
参数：a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
-/
protected lemma HasSubst.pow {n : ℕ} (hn : n ≠ 0) {a : σ → MvPowerSeries τ S} (h : HasSubst a) :
    HasSubst (a ^ n) :=
  hasSubstIdeal.pow_mem_of_mem h _ (by lia)
/-
**MvPowerSeries.HasSubst.X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst
`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRing S] {n : ℕ},   n ≠ 0 → MvP
owerSeries.HasSubst fun s => MvPowerSeries.X s ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.pow`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_
5} [inst : CommRing S] {n : ℕ},   n ≠ 0 → ∀ {a : σ → MvPowerSeries τ S}, MvPower
Series.HasSubst …
· 使用定理 `MvPowerSeries.HasSubst.X`：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRi
ng S], MvPowerSeries.HasSubst fun s => MvPowerSeries.X s
-/
protected theorem HasSubst.X_pow {n : ℕ} (hn : n ≠ 0) :
    HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S) ^ n) :=
  HasSubst.X.pow (by lia)
/-
**MvPowerSeries.HasSubst.truncTotal** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.Has
Subst`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] {a : σ 
→ MvPowerSeries τ S} {x : σ → ℕ}   [inst_1 : Finite τ],   MvPowerSeries.HasSubst
 a → MvPowerSeries.HasSubst fun i => ↑((MvPowerSeries.truncTotal (x i)) (a i))
参数：(MvPowerSeries.truncTotal (x i)) (a i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPolynomial.coeff_coe`：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff 
n ↑φ = coeff n φ
· 使用定理 `MvPolynomial.constantCoeff_eq`：constantCoeff_eq : (constantCoeff : MvPol
ynomial σ R -> R) = coeff 0
· 使用定理 `MvPowerSeries.constantCoeff_truncTotal_eq_ite`：constantCoeff_truncTotal_
eq_ite : (truncTotal n p).constantCoeff = if 0 < n then p.constantCoeff else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPowerSeries.HasSubst.const_coeff`：∀ {σ : Type u_1} {τ : Type u_4} {S :
 Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasS
ubst a → ∀ (s : σ), IsNi…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `MvPowerSeries.HasSubst.coeff_zero`：∀ {σ : Type u_1} {τ : Type u_4} {S : 
Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasSu
bst a → ∀ (d : τ →₀ ℕ),…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.coeff_truncTotal_eq_ite`：coeff_truncTotal_eq_ite : (truncT
otal n p).coeff x = if x.degree < n then p.coeff x else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma HasSubst.truncTotal {a : σ → MvPowerSeries τ S} {x : σ → ℕ} [Finite τ]
    (ha : HasSubst a) : HasSubst (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries) where
  const_coeff i := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, constantCoeff_truncTotal_eq_ite]
    split_ifs <;> simp [ha.const_coeff i]
  coeff_zero d :=
    (ha.coeff_zero d).subset fun i => by contrapose; simp +contextual [coeff_truncTotal_eq_ite]

/-- Substitution of power series into a power series

It coincides with evaluation when `f` is a polynomial, or under `HasSubst a`.
Otherwise, it is given the dummy value `0`. -/
/-
**MvPowerSeries.subst** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：subst (a : σ -> MvPowerSeries τ S) (f : MvPowerSeries σ R) : MvPowerSeries
 τ S
参数：a : σ -> MvPowerSeries τ S；f : MvPowerSeries σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Substitution of power series into a power series

It coincides with evaluation when `f` is a polynomial, or under `HasSubst a`.
Otherwise, it is given the dummy value `0`.
-/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  eval₂ (algebraMap _ _) a f
/-
**MvPowerSeries.subst_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subst_eq_eval₂
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    (subst : (σ → MvPowerSeries τ S) → (MvPowerSeries σ R) → _) = eval₂ (algebraMap _ _) := by
  ext; simp +instances [subst, DiscreteUniformity.eq_bot]
/-
**MvPowerSeries.subst_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_coe (p : MvPolynomial σ R) : subst (R
参数：p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.subst_eq_eval₂`：subst_eq_eval₂ [UniformSpace R] [DiscreteU
niformity R] [UniformSpace S] [DiscreteUniformity S] : (subst : (σ -> MvPowerSer
ies τ S) -> (MvPow…
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `MvPowerSeries.eval₂_coe`：eval₂_coe (f : MvPolynomial σ R) : MvPowerSerie
s.eval₂ φ a f = MvPolynomial.eval₂ φ a f
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
-/
theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [subst_eq_eval₂, eval₂_coe, MvPolynomial.aeval_def]

variable {a : σ → MvPowerSeries τ S}

/-- For `HasSubst a`, `MvPowerSeries.subst` is an algebra morphism. -/
/-
**MvPowerSeries.substAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom (ha : HasSubst a) : MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ S
参数：ha : HasSubst a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `HasSubst a`, `MvPowerSeries.subst` is an algebra morphism.
-/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.aeval ha.hasEval

/-- Rewrite `MvPowerSeries.substAlgHom` as `MvPowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons. -/
/-
**MvPowerSeries.substAlgHom_eq_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom_eq_aeval [UniformSpace R] [DiscreteUniformity R] [UniformSpace
 S] [DiscreteUniformity S] (ha : HasSubst a) : (substAlgHom ha : MvPowerSeries σ
 R -> MvPowerSeries τ S) = MvPowerSeries.aeval ha.hasEval
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`：hasSubst_iff_has
Eval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] : HasSubst a 
↔ HasEval a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteUniformity.eq_bot`：∀ {X : Type u_1} {u : UniformSpace X} [self :
 DiscreteUniformity X], u = ⊥

--- 原说明 ---
Rewrite `MvPowerSeries.substAlgHom` as `MvPowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons.
-/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : MvPowerSeries σ R → MvPowerSeries τ S) = MvPowerSeries.aeval ha.hasEval := by
  simp only [substAlgHom, coe_aeval ha.hasEval]
  convert! coe_aeval (R := R) (hasSubst_iff_hasEval_of_discreteTopology.mp ha) <;>
  exact DiscreteUniformity.eq_bot.symm

@[simp]
/-
**MvPowerSeries.coe_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coe_substAlgHom (ha : HasSubst a) : ⇑(substAlgHom ha) = subst (R
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `MvPowerSeries.subst_eq_eval₂`：subst_eq_eval₂ [UniformSpace R] [DiscreteU
niformity R] [UniformSpace S] [DiscreteUniformity S] : (subst : (σ -> MvPowerSer
ies τ S) -> (MvPow…
-/
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [substAlgHom_eq_aeval, coe_aeval ha.hasEval, subst_eq_eval₂]
/-
**MvPowerSeries.subst_self** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_self : subst (MvPowerSeries.X : σ -> MvPowerSeries σ R) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.X`：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRi
ng S], MvPowerSeries.HasSubst fun s => MvPowerSeries.X s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
（共 34 条，此处仅展示前 30 条）
-/
theorem subst_self : subst (MvPowerSeries.X : σ → MvPowerSeries σ R) = id := by
  rw [← coe_substAlgHom HasSubst.X]
  let : UniformSpace R := ⊥
  ext1 f
  simp only [substAlgHom_eq_aeval]
  have := aeval_unique (ε := AlgHom.id R (MvPowerSeries σ R)) continuous_id
  rw [DFunLike.ext_iff] at this
  exact this f

@[simp]
/-
**MvPowerSeries.substAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom_apply (ha : HasSubst a) (f : MvPowerSeries σ R) : substAlgHom 
ha f = subst a f
参数：ha : HasSubst a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
-/
theorem substAlgHom_apply (ha : HasSubst a) (f : MvPowerSeries σ R) :
    substAlgHom ha f = subst a f := by
  rw [coe_substAlgHom]
/-
**MvPowerSeries.subst_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) : subst a (f + g) = 
subst a f + subst a g
参数：ha : HasSubst a；f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  simp only [← substAlgHom_apply ha, map_add]
/-
**MvPowerSeries.subst_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_sub (ha : HasSubst a) (f g : MvPowerSeries σ R) : subst a (f - g) = 
subst a f - subst a g
参数：ha : HasSubst a；f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_sub (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f - g) = subst a f - subst a g := by
  simp_rw [← substAlgHom_apply ha, map_sub]
/-
**MvPowerSeries.subst_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) : subst a (f * g) = 
subst a f * subst a g
参数：ha : HasSubst a；f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  simp only [← substAlgHom_apply ha, map_mul]
/-
**MvPowerSeries.subst_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : Nat) : subst a (f
 ^ n) = (subst a f) ^ n
参数：ha : HasSubst a；f : MvPowerSeries σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f) ^ n := by
  simp only [← substAlgHom_apply ha, map_pow]
/-
**MvPowerSeries.subst_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) : subst a (r 
• f) = r • (subst a f)
参数：ha : HasSubst a；r : A；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `AlgHom.map_smul_of_tower`：map_smul_of_tower {R'} [SMul R' A] [SMul R' B]
 [LinearMap.CompatibleSMul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  simp only [← substAlgHom_apply ha, AlgHom.map_smul_of_tower]
/-
**MvPowerSeries.substAlgHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) : substAlgHom (R
参数：ha : HasSubst a；p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.aeval_coe`：aeval_coe (ha : HasEval a) (p : MvPolynomial σ 
R) : aeval ha (p : MvPowerSeries σ R) = p.aeval a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p := by
  simp [substAlgHom]
/-
**MvPowerSeries.substAlgHom_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom_X (ha : HasSubst a) (s : σ) : substAlgHom (R
参数：ha : HasSubst a；s : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coe_X`：coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerS
eries σ R) = MvPowerSeries.X s
· 使用定理 `MvPowerSeries.substAlgHom_coe`：substAlgHom_coe (ha : HasSubst a) (p : Mv
Polynomial σ R) : substAlgHom (R
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
-/
theorem substAlgHom_X (ha : HasSubst a) (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe ha, MvPolynomial.aeval_X]
/-
**MvPowerSeries.substAlgHom_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：substAlgHom_monomial (ha : HasSubst a) (e : σ ->₀ Nat) (r : R) : substAlgH
om ha (monomial e r) = (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n =
> (a s) ^ n))
参数：ha : HasSubst a；e : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coe_monomial`：coe_monomial (n : σ ->₀ Nat) (a : R) : (monom
ial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a
· 使用定理 `MvPowerSeries.substAlgHom_coe`：substAlgHom_coe (ha : HasSubst a) (p : Mv
Polynomial σ R) : substAlgHom (R
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
-/
theorem substAlgHom_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    substAlgHom ha (monomial e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial, substAlgHom_coe, MvPolynomial.aeval_monomial]

@[simp]
/-
**MvPowerSeries.subst_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_C (r : S) : (C r).subst a = MvPowerSeries.C r
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.eval₂_C`：eval₂_C (r : R) : eval₂ φ a (C r) = φ r
· 使用定理 `MvPowerSeries.algebraMap_apply`：algebraMap_apply {r : R} : algebraMap R 
(MvPowerSeries σ A) r = C (algebraMap R A r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subst_C (r : S) :
    (C r).subst a = MvPowerSeries.C r := by
  simp [subst, algebraMap_apply]

@[simp]
/-
**MvPowerSeries.subst_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_X (ha : HasSubst a) (s : σ) : subst (R
参数：ha : HasSubst a；s : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.substAlgHom_X`：substAlgHom_X (ha : HasSubst a) (s : σ) : s
ubstAlgHom (R
-/
theorem subst_X (ha : HasSubst a) (s : σ) :
    subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha, substAlgHom_X]
/-
**MvPowerSeries.subst_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_monomial (ha : HasSubst a) (e : σ ->₀ Nat) (r : R) : subst a (monomi
al e r) = (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n => (a s) ^ n))
参数：ha : HasSubst a；e : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.substAlgHom_monomial`：substAlgHom_monomial (ha : HasSubst 
a) (e : σ ->₀ Nat) (r : R) : substAlgHom ha (monomial e r) = (algebraMap R (MvPo
werSeries τ S) r) * (e.p…
-/
theorem subst_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    subst a (monomial e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← coe_substAlgHom ha, substAlgHom_monomial]
/-
**MvPowerSeries.continuous_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：continuous_subst (ha : HasSubst a) [UniformSpace R] [DiscreteUniformity R]
 [UniformSpace S] [DiscreteUniformity S] : Continuous (subst a : MvPowerSeries σ
 R -> MvPowerSeries τ S)
参数：ha : HasSubst a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.subst_eq_eval₂`：subst_eq_eval₂ [UniformSpace R] [DiscreteU
niformity R] [UniformSpace S] [DiscreteUniformity S] : (subst : (σ -> MvPowerSer
ies τ S) -> (MvPow…
· 使用定理 `MvPowerSeries.continuous_eval₂`：continuous_eval₂ (hφ : Continuous φ) (ha
 : HasEval a) : Continuous (eval₂ φ a : MvPowerSeries σ R -> S)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
-/
theorem continuous_subst (ha : HasSubst a)
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) := by
  rw [subst_eq_eval₂]
  exact continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval
/-
**MvPowerSeries.coeff_subst_finite** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Na
t) : (fun d => coeff d f • (coeff e (d.prod fun s e => (a s) ^ e))).HasFiniteSup
port
参数：ha : HasSubst a；f : MvPowerSeries σ R；e : τ ->₀ Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasFiniteSupport_of_discreteTopology`：∀ {α : Type u_5} [inst : 
AddCommGroup α] [inst_1 : TopologicalSpace α] [DiscreteTopology α] {β : Type u_6
} (f : β → α),   Summable f → Funct…
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `MvPowerSeries.hasSum_aeval`：hasSum_aeval (ha : HasEval a) (f : MvPowerSe
ries σ R) : HasSum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s
) ^ e)) (MvPower…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semirin
g R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.coeff (R
-/
theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    (fun d ↦ coeff d f • (coeff e (d.prod fun s e => (a s) ^ e))).HasFiniteSupport :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  Summable.hasFiniteSupport_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e)).summable
/-
**MvPowerSeries.coeff_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Nat) : co
eff e (subst a f) = finsum (fun d => coeff d f • (coeff e (d.prod fun s e => (a 
s) ^ e)))
参数：ha : HasSubst a；f : MvPowerSeries σ R；e : τ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `MvPowerSeries.hasSum_aeval`：hasSum_aeval (ha : HasEval a) (f : MvPowerSe
ries σ R) : HasSum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s
) ^ e)) (MvPower…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semirin
g R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.coeff (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 44 条，此处仅展示前 30 条）
-/
theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff e (subst a f) =
      finsum (fun d ↦ coeff d f • (coeff e (d.prod fun s e => (a s) ^ e))) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  have := ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e))
  simp [← coe_substAlgHom ha, substAlgHom, ← this.tsum_eq,
    tsum_eq_finsum (coeff_subst_finite ha f e)]
/-
**MvPowerSeries.constantCoeff_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) : constantCo
eff (subst a f) = finsum (fun d => coeff d f • (constantCoeff (d.prod fun s e =>
 (a s) ^ e)))
参数：ha : HasSubst a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) =
      finsum (fun d ↦ coeff d f • (constantCoeff (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]
/-
**MvPowerSeries.constantCoeff_subst_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：constantCoeff_subst_eq_zero (ha : HasSubst a) (ha' : forall i, (a i).const
antCoeff = 0) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : MvPowerSeries
.constantCoeff (subst a f) = 0
参数：ha : HasSubst a；ha' : forall i, (a i).constantCoeff = 0；hf : f.constantCoeff 
= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_subst`：constantCoeff_subst (ha : HasSubst a)
 (f : MvPowerSeries σ R) : constantCoeff (subst a f) = finsum (fun d => coeff d 
f • (constantCoeff (d.p…
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem constantCoeff_subst_eq_zero (ha : HasSubst a) (ha' : ∀ i, (a i).constantCoeff = 0)
    {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    MvPowerSeries.constantCoeff (subst a f) = 0 := by
  rw [constantCoeff_subst ha, finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  · have : constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      simpa [map_finsuppProd, ha'] using!
        Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this, smul_zero]
/-
**MvPowerSeries.map_algebraMap_eq_subst_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：map_algebraMap_eq_subst_X (f : MvPowerSeries σ R) : map (algebraMap R S) f
 = subst X f
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_map`：coeff_map (n : σ ->₀ Nat) (φ : MvPowerSeries σ 
R) : coeff n (map f φ) = f (coeff n φ)
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.X`：∀ {σ : Type u_1} {S : Type u_5} [inst : CommRi
ng S], MvPowerSeries.HasSubst fun s => MvPowerSeries.X s
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.monomial_one_eq`：∀ {σ : Type u_1} {R : Type u_2} [inst : C
ommSemiring R] (e : σ →₀ ℕ),   (MvPowerSeries.monomial e) 1 = e.prod fun s n => 
MvPowerSeries.X s ^…
· 使用定理 `MvPowerSeries.coeff_monomial_ne`：coeff_monomial_ne {m n : σ ->₀ Nat} (h 
: m != n) (a : R) : coeff m (monomial n a) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `algebra_compatible_smul`：algebra_compatible_smul (r : R) (m : M) : r • m
 = (algebraMap R A) r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem map_algebraMap_eq_subst_X (f : MvPowerSeries σ R) :
    map (algebraMap R S) f = subst X f := by
  ext e
  rw [coeff_map, coeff_subst HasSubst.X f e, finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne hd.symm, smul_zero]

omit [Algebra R S] in
/-
**MvPowerSeries.map_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_subst {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S} (f
 : MvPowerSeries σ R) : (f.subst a).map h = (f.map h).subst (fun i => (a i).map 
h)
参数：ha : HasSubst a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.map`：∀ {σ : Type u_1} {R : Type u_3} [inst : Comm
Ring R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   {a : σ → MvPowerSe
ries τ R},   MvP…
· 使用定理 `MvPowerSeries.coeff_map`：coeff_map (n : σ ->₀ Nat) (φ : MvPowerSeries σ 
R) : coeff n (map f φ) = f (coeff n φ)
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…
· 使用定理 `MvPowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (
f : MvPowerSeries σ R) (e : τ ->₀ Nat) : (fun d => coeff d f • (coeff e (d.prod 
fun s e => (a s) ^ e))…
· 使用定理 `finsum_congr`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M] {
f g : α → M}, (∀ (x : α), f x = g x) → finsum f = finsum g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_subst {a : σ → MvPowerSeries τ R} (ha : HasSubst a) {h : R →+* S}
    (f : MvPowerSeries σ R) :
    (f.subst a).map h = (f.map h).subst (fun i => (a i).map h) := by
  ext n
  have {r : R} : h r = h.toAddMonoidHom r := rfl
  rw [coeff_subst (ha.map h), coeff_map, coeff_subst ha, this, AddMonoidHom.map_finsum _
    (coeff_subst_finite ha _ _), finsum_congr]
  intro d
  simp [smul_eq_mul, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul,
    ← coeff_map, Finsupp.prod]
/-
**MvPowerSeries.subst_zero_eq_C_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `MvPower
Series`。
形式化陈述：subst_zero_eq_C_constantCoeff {f : MvPowerSeries σ R} : f.subst (0 : σ -> 
MvPowerSeries τ S) = (C f.constantCoeff).map (algebraMap R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MvPowerSeries.coeff_map`：coeff_map (n : σ ->₀ Nat) (φ : MvPowerSeries σ 
R) : coeff n (map f φ) = f (coeff n φ)
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.support_nonempty_iff`：support_nonempty_iff {f : α ->₀ M} : f.sup
port.Nonempty ↔ f != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `MvPowerSeries.coeff_one`：coeff_one [DecidableEq σ] : coeff n (1 : MvPowe
rSeries σ R) = if n = 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MvPowerSeries.coeff_C_of_ne_zero`：coeff_C_of_ne_zero {n : σ ->₀ Nat} (h 
: n != 0) (a : R) : coeff n (C a) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 31 条，此处仅展示前 30 条）
-/
lemma subst_zero_eq_C_constantCoeff {f : MvPowerSeries σ R} :
    f.subst (0 : σ → MvPowerSeries τ S) = (C f.constantCoeff).map (algebraMap R S) := by
  classical
  ext n
  rw [coeff_subst (by simp [hasSubst_def]), coeff_map, finsum_eq_single _ 0]
  · by_cases hn : n = 0
    · simp [hn, Algebra.algebraMap_eq_smul_one]
    simp [coeff_C_of_ne_zero hn, coeff_one, hn]
  intro d hd
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  simp [Finsupp.prod, Finset.prod_eq_zero hi, coeff_zero, zero_pow <| d.mem_support_iff.mp hi]

@[simp]
/-
**MvPowerSeries.subst_zero_of_constantCoeff_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPo
werSeries`。
形式化陈述：subst_zero_of_constantCoeff_zero {f : MvPowerSeries σ R} (hf : f.constantC
oeff = 0) : f.subst (0 : σ -> MvPowerSeries τ S) = 0
参数：hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.subst_zero_eq_C_constantCoeff`：subst_zero_eq_C_constantCoe
ff {f : MvPowerSeries σ R} : f.subst (0 : σ -> MvPowerSeries τ S) = (C f.constan
tCoeff).map (algebraMap R S)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subst_zero_of_constantCoeff_zero {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    f.subst (0 : σ → MvPowerSeries τ S) = 0 := by
  simp [subst_zero_eq_C_constantCoeff, hf]
/-
**MvPowerSeries.HasSubst.cons_subst_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `MvPower
Series.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {f : MvPowerSeries (Fi
n 2) R} (i j k : σ),   MvPowerSeries.constantCoeff f = 0 →     MvPowerSeries.Has
Subst ![MvPowerSeries.subst ![MvPowerSeries.X i, MvPowerSeries.X j] f, MvPowerSe
ries.X k]
参数：Fin 2；i j k : σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.X_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : Comm
Ring R] {i j : σ},   MvPowerSeries.HasSubst ![MvPowerSeries.X i, MvPowerSeries.X
 j]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma HasSubst.cons_subst_zero_left {f : MvPowerSeries (Fin 2) R} (i j k : σ)
    (hF : constantCoeff f = 0) : HasSubst (![subst ![X i, X j] f, X k]) (S := R) :=
  hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]
/-
**MvPowerSeries.HasSubst.cons_subst_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `MvPowe
rSeries.HasSubst`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] {f : MvPowerSeries (Fi
n 2) R} (i j k : σ),   MvPowerSeries.constantCoeff f = 0 →     MvPowerSeries.Has
Subst ![MvPowerSeries.X i, MvPowerSeries.subst ![MvPowerSeries.X j, MvPowerSerie
s.X k] f]
参数：Fin 2；i j k : σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.X_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : Comm
Ring R] {i j : σ},   MvPowerSeries.HasSubst ![MvPowerSeries.X i, MvPowerSeries.X
 j]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma HasSubst.cons_subst_zero_right {f : MvPowerSeries (Fin 2) R} (i j k : σ)
    (hF : constantCoeff f = 0) : HasSubst ![X i, subst ![X j, X k] f] (S := R) :=
  hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]

variable
    {T : Type*} [CommRing T]
    [UniformSpace T] [T2Space T] [CompleteSpace T]
    [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T] [Algebra R T]
    {ε : MvPowerSeries τ S →ₐ[R] T}
/-
**MvPowerSeries.comp_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：comp_substAlgHom [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] 
[DiscreteUniformity S] (ha : HasSubst a) (hε : Continuous ε) : ε.comp (substAlgH
om ha) = aeval (ha.hasEval.map hε)
参数：ha : HasSubst a；hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MvPowerSeries.comp_aeval`：comp_aeval (ha : HasEval a) {T : Type*} [CommR
ing T] [UniformSpace T] [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTop
ology T T] [T2…
-/
theorem comp_substAlgHom
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε.comp (substAlgHom ha) = aeval (ha.hasEval.map hε) := by
  ext f
  simp only [AlgHom.coe_comp, substAlgHom_eq_aeval ha]
  exact DFunLike.congr_fun (comp_aeval ha.hasEval hε) f
/-
**MvPowerSeries.comp_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：comp_subst [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [Discr
eteUniformity S] (ha : HasSubst a) (hε : Continuous ε) : ε ∘ (subst a) = aeval (
R
参数：ha : HasSubst a；hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.comp_substAlgHom`：comp_substAlgHom [UniformSpace R] [Discr
eteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst a) (hε :
 Continuous ε) : ε.c…
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
-/
theorem comp_subst [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε ∘ (subst a) = aeval (R := R) (ha.hasEval.map hε) := by
  rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]
/-
**MvPowerSeries.comp_subst_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：comp_subst_apply [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] 
[DiscreteUniformity S] (ha : HasSubst a) (hε : Continuous ε) (f : MvPowerSeries 
σ R) : ε (subst a f) = aeval (R
参数：ha : HasSubst a；hε : Continuous ε；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `MvPowerSeries.comp_subst`：comp_subst [UniformSpace R] [DiscreteUniformit
y R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst a) (hε : Continuous 
ε) : ε ∘ (subs…
-/
theorem comp_subst_apply
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) (f : MvPowerSeries σ R) :
    ε (subst a f) = aeval (R := R) (ha.hasEval.map hε) f :=
  congr_fun (comp_subst ha hε) f

variable [Algebra S T] [IsScalarTower R S T]
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_subst
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) {b : τ → T} (hb : HasEval b) (f : MvPowerSeries σ R) :
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f := by
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

variable {υ : Type*}
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {b : τ → MvPowerSeries υ T}
/-
**MvPowerSeries.IsNilpotent_subst** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：IsNilpotent_subst (ha : HasSubst a) {f : MvPowerSeries σ R} (hf : IsNilpot
ent f.constantCoeff) : IsNilpotent (constantCoeff (f.subst a))
参数：ha : HasSubst a；hf : IsNilpotent f.constantCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_subst`：constantCoeff_subst (ha : HasSubst a)
 (f : MvPowerSeries σ R) : constantCoeff (subst a f) = finsum (fun d => coeff d 
f • (constantCoeff (d.p…
· 使用定理 `isNilpotent_finsum`：isNilpotent_finsum {ι : Type*} {f : ι -> R} (hf : fo
rall b, IsNilpotent (f b)) : IsNilpotent (finsum f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `IsNilpotent.smul`：IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S]
 [MulActionWithZero R S] [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha
 : IsN…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.support_nonempty_iff`：support_nonempty_iff {f : α ->₀ M} : f.sup
port.Nonempty ↔ f != 0
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用引理 `IsNilpotent.pow_iff_pos`：IsNilpotent.pow_iff_pos {n} {S : Type*} [Monoid
WithZero S] {x : S} (hn : n != 0) : IsNilpotent (x ^ n) ↔ IsNilpotent x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `MvPowerSeries.HasSubst.const_coeff`：∀ {σ : Type u_1} {τ : Type u_4} {S :
 Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasS
ubst a → ∀ (s : σ), IsNi…
-/
lemma IsNilpotent_subst (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent f.constantCoeff) :
    IsNilpotent (constantCoeff (f.subst a)) := by
  classical
  rw [constantCoeff_subst ha]
  refine isNilpotent_finsum fun d => ?_
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simpa using IsNilpotent.map hf (algebraMap R S)
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  rw [Finsupp.prod, map_prod, ← Finset.prod_erase_mul _ _ hi, ← algebraMap_smul S,
    smul_eq_mul, ← mul_assoc, map_pow]
  exact Commute.isNilpotent_mul_left (Commute.all _ _)
    <| (IsNilpotent.pow_iff_pos (d.mem_support_iff.mp hi)).mpr (ha.const_coeff i)
/-
**MvPowerSeries.IsNilpotent_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：IsNilpotent_substAlgHom (ha : HasSubst a) {f : MvPowerSeries σ R} (hf : Is
Nilpotent (constantCoeff f)) : IsNilpotent (constantCoeff (substAlgHom ha f))
参数：ha : HasSubst a；hf : IsNilpotent (constantCoeff f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用引理 `MvPowerSeries.IsNilpotent_subst`：IsNilpotent_subst (ha : HasSubst a) {f 
: MvPowerSeries σ R} (hf : IsNilpotent f.constantCoeff) : IsNilpotent (constantC
oeff (f.subst a))
-/
theorem IsNilpotent_substAlgHom (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) :
    IsNilpotent (constantCoeff (substAlgHom ha f)) := by
  simpa using IsNilpotent_subst ha hf
/-
**MvPowerSeries.HasSubst.comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubst`
。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u_5} [inst : CommRing S] {a : σ 
→ MvPowerSeries τ S} {υ : Type u_7}   {T : Type u_8} [inst_1 : CommRing T] [inst
_2 : Algebra S T] {b : τ → MvPowerSeries υ T},   MvPowerSeries.HasSubst a →     
∀ (hb : MvPowerSeries.HasSubst b), MvPowerSeries.HasSubst fun s => (MvPowerSerie
s.substAlgHom hb) (a s)
参数：hb : MvPowerSeries.HasSubst b；MvPowerSeries.substAlgHom hb；a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.IsNilpotent_substAlgHom`：IsNilpotent_substAlgHom (ha : Has
Subst a) {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsNilpot
ent (constantCoeff (substAl…
· 使用定理 `MvPowerSeries.HasSubst.const_coeff`：∀ {σ : Type u_1} {τ : Type u_4} {S :
 Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasS
ubst a → ∀ (s : σ), IsNi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPowerSeries.coeff_zero_iff`：coeff_zero_iff [TopologicalSpace S] [Discr
eteTopology S] : Filter.Tendsto a Filter.cofinite (nhds 0) ↔ forall d : τ ->₀ Na
t, {s | (a s).coef…
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `MvPowerSeries.continuous_subst`：continuous_subst (ha : HasSubst a) [Unif
ormSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] : Con
tinuous (subst a : M…
· 使用定理 `MvPowerSeries.HasEval.tendsto_zero`：∀ {σ : Type u_1} {S : Type u_3} [ins
t : CommRing S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEv
al a → Filter.Tendsto a …
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
-/
theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_substAlgHom hb (ha.const_coeff s)
  coeff_zero := by
    let : UniformSpace S := ⊥
    let : UniformSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simpa [← map_zero (substAlgHom (R := S) hb)] using! (continuous_subst hb).continuousAt
/-
**MvPowerSeries.substAlgHom_comp_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries`。
形式化陈述：substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) : ((subst
AlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb)
参数：ha : HasSubst a；hb : HasSubst b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.comp_aeval`：comp_aeval (ha : HasEval a) {T : Type*} [CommR
ing T] [UniformSpace T] [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTop
ology T T] [T2…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.continuous_subst`：continuous_subst (ha : HasSubst a) [Unif
ormSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] : Con
tinuous (subst a : M…
-/
theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace T := ⊥
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simpa [AlgHom.coe_restrictScalars'] using continuous_subst (R := S) hb
/-
**MvPowerSeries.substAlgHom_comp_substAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b) (f 
: MvPowerSeries σ R) : (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.com
p hb) f
参数：ha : HasSubst a；hb : HasSubst b；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.comp`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u
_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {υ : Type u_7}   {T : Type u
_8} [inst_1 : Com…
· 使用定理 `MvPowerSeries.substAlgHom_comp_substAlgHom`：substAlgHom_comp_substAlgHom
 (ha : HasSubst a) (hb : HasSubst b) : ((substAlgHom hb).restrictScalars R).comp
 (substAlgHom ha) = substAlgHom …
-/
theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b)
    (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f
/-
**MvPowerSeries.subst_comp_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) : (subst b) ∘ (subst 
a) = subst (R
参数：ha : HasSubst a；hb : HasSubst b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.comp`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u
_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {υ : Type u_7}   {T : Type u
_8} [inst_1 : Com…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [i
nst : CommRing R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   [inst_2 
: Algebra R S] {a a_1 : σ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.substAlgHom_comp_substAlgHom`：substAlgHom_comp_substAlgHom
 (ha : HasSubst a) (hb : HasSubst b) : ((substAlgHom hb).restrictScalars R).comp
 (substAlgHom ha) = substAlgHom …
-/
theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  simpa [funext_iff, DFunLike.ext_iff] using substAlgHom_comp_substAlgHom (R := R) ha hb
/-
**MvPowerSeries.subst_comp_subst_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSer
ies σ R) : subst b (subst a f) = subst (fun s => subst b (a s)) f
参数：ha : HasSubst a；hb : HasSubst b；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.subst_comp_subst`：subst_comp_subst (ha : HasSubst a) (hb :
 HasSubst b) : (subst b) ∘ (subst a) = subst (R
-/
theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section

variable (w : τ → ℕ)

/-
**MvPowerSeries.le_weightedOrder_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：le_weightedOrder_subst (ha : HasSubst a) (f : MvPowerSeries σ R) : ⨅ (d : 
σ ->₀ Nat) (_ : coeff d f != 0), d.weight (weightedOrder w ∘ a) <= (f.subst a).w
eightedOrder w
参数：ha : HasSubst a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MvPowerSeries.le_weightedOrder_pow`：le_weightedOrder_pow (n : Nat) : n •
 f.weightedOrder w <= (f ^ n).weightedOrder w
· 使用定理 `MvPowerSeries.le_weightedOrder_prod`：le_weightedOrder_prod {R : Type*} [
CommSemiring R] {ι : Type*} (w : σ -> Nat) (f : ι -> MvPowerSeries σ R) (s : Fin
set ι) : ∑ i in s, (f i).…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem le_weightedOrder_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    ⨅ (d : σ →₀ ℕ) (_ : coeff d f ≠ 0), d.weight (weightedOrder w ∘ a) ≤
      (f.subst a).weightedOrder w := by
  apply MvPowerSeries.le_weightedOrder
  intro d hd
  rw [coeff_subst ha, finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hfx : f.coeff x = 0
  · simp [hfx]
  rw [coeff_eq_zero_of_lt_weightedOrder w, smul_zero]
  refine hd.trans_le (((biInf_le _ hfx).trans ?_).trans (le_weightedOrder_prod ..))
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply]
  exact Finset.sum_le_sum fun i hi ↦ .trans (by simp) (le_weightedOrder_pow ..)
/-
**MvPowerSeries.le_weightedOrder_subst_of_forall_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_subst_of_forall_ne_zero (ha : HasSubst a) (ha0 : forall i
, a i != 0) (f : MvPowerSeries σ R) : f.weightedOrder (ENat.toNat ∘ weightedOrde
r w ∘ a) <= (f.subst a).weightedOrder w
参数：ha : HasSubst a；ha0 : forall i, a i != 0；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPowerSeries.weightedOrder_le`：weightedOrder_le {d : σ ->₀ Nat} (h : co
eff d f != 0) : f.weightedOrder w <= weight w d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPowerSeries.ne_zero_iff_weightedOrder_finite`：ne_zero_iff_weightedOrde
r_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MvPowerSeries.le_weightedOrder_subst`：le_weightedOrder_subst (ha : HasSu
bst a) (f : MvPowerSeries σ R) : ⨅ (d : σ ->₀ Nat) (_ : coeff d f != 0), d.weigh
t (weightedOrder w ∘ a) <=…
-/
theorem le_weightedOrder_subst_of_forall_ne_zero
    (ha : HasSubst a) (ha0 : ∀ i, a i ≠ 0) (f : MvPowerSeries σ R) :
    f.weightedOrder (ENat.toNat ∘ weightedOrder w ∘ a) ≤ (f.subst a).weightedOrder w := by
  refine .trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  refine fun i hi ↦ (weightedOrder_le _ hi).trans ?_
  simp [Finsupp.weight_apply, Finsupp.sum, (ne_zero_iff_weightedOrder_finite _).mp (ha0 _)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.le_order_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_subst (ha : HasSubst a) (f : MvPowerSeries σ R) : (⨅ i, (a i).ord
er) * f.order <= (f.subst a).order
参数：ha : HasSubst a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `MvPowerSeries.order_le`：order_le {d : σ ->₀ Nat} (h : coeff d f != 0) : 
f.order <= degree d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_le_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteSemilattice
Inf α] {a : α} {s : ι → α},   iInf s ≤ a ↔ ∀ (b : α), (∀ (i : ι), b ≤ s i) → b ≤
 …
· 使用定理 `MvPowerSeries.le_weightedOrder_subst`：le_weightedOrder_subst (ha : HasSu
bst a) (f : MvPowerSeries σ R) : ⨅ (d : σ ->₀ Nat) (_ : coeff d f != 0), d.weigh
t (weightedOrder w ∘ a) <=…
-/
theorem le_order_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    (⨅ i, (a i).order) * f.order ≤ (f.subst a).order := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ ha _)
  simp only [ne_eq, le_iInf_iff]
  intro i hi
  trans (⨅ (i : σ), (order ∘ a) i) * ↑i.degree
  · refine mul_le_mul_right (order_le hi) _
  · simp only [Function.comp_apply, order, Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Nat.cast_sum, Finset.mul_sum, Finsupp.weight_apply, nsmul_eq_mul]
    exact Finset.sum_le_sum fun j hj => by
      simp [mul_comm, mul_le_mul_right (iInf_le_iff.mpr fun _ a ↦ a j)]

end

section truncTotal

open Finset

variable {f : MvPowerSeries σ R} [Finite τ] {x : σ → ℕ} {k : ℕ}

/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le** 是 Mathli
b 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le (ha : HasSubst a) (h
x : forall i, k <= x i) : (f.subst a).truncTotal k = (f.subst fun i => ((a i).tr
uncTotal (x i)).toMvPowerSeries).truncTotal k
参数：ha : HasSubst a；hx : forall i, k <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.truncTotal`：∀ {σ : Type u_1} {τ : Type u_4} {S : 
Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {x : σ → ℕ}   [inst_1 
: Finite τ],   MvPowerS…
· 使用定理 `finsum_congr`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M] {
f g : α → M}, (∀ (x : α), f x = g x) → finsum f = finsum g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MvPowerSeries.coeff_prod`：coeff_prod [DecidableEq ι] [DecidableEq σ] (f 
: ι -> MvPowerSeries σ R) (d : σ ->₀ Nat) (s : Finset ι) : coeff d (∏ j in s, f 
j) = ∑ l in fi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_finsuppAntidiag`：∀ {ι : Type u_1} {μ : Type u_2} [inst : Deci
dableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ]   [ins
t_3 : DecidableE…
· 使用引理 `Finsupp.degree_mono`：degree_mono {R : Type*} [AddCommMonoid R] [PartialO
rder R] [CanonicallyOrderedAdd R] : Monotone (Finsupp.degree (σ
· 使用定理 `Finset.single_le_sum_of_canonicallyOrdered`：∀ {ι : Type u_1} {M : Type u
_4} [inst : AddCommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f 
: ι → M}   {s : Finset ι} {i : ι…
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `MvPowerSeries.coeff_truncTotal_pow`：coeff_truncTotal_pow (h : x.degree <
 n) : ((p.truncTotal n ^ m)).coeff x = (p ^ m).coeff x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 58 条，此处仅展示前 30 条）
-/
theorem truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le (ha : HasSubst a)
    (hx : ∀ i, k ≤ x i) :
    (f.subst a).truncTotal k = (f.subst
      fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries).truncTotal k := by
  classical
  ext d
  by_cases hd : d.degree < k
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, coeff_subst ha, coeff_subst, finsum_congr]
    · intro n
      simp_rw [Finsupp.prod, coeff_prod]
      congr! 3 with l hl i hi
      obtain ⟨hl₁, -⟩ := mem_finsuppAntidiag.mp hl
      have : (l i).degree ≤ d.degree :=
        hl₁ ▸ Finsupp.degree_mono (single_le_sum_of_canonicallyOrdered hi)
      exact_mod_cast (coeff_truncTotal_pow _ (by nlinarith [hx i])).symm
    · exact ha.truncTotal
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_subst_sum (ha : HasSubst a) (ha₁ : forall i
, (a i).constantCoeff = 0) : truncTotal k (f.subst a) = ((∑ i in range k, (f.hom
ogeneousComponent i)).subst a).truncTotal k
参数：ha : HasSubst a；ha₁ : forall i, (a i).constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (
f : MvPowerSeries σ R) (e : τ ->₀ Nat) : (fun d => coeff d f • (coeff e (d.prod 
fun s e => (a s) ^ e))…
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPowerSeries.coeff_homogeneousComponent`：coeff_homogeneousComponent (p 
: Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (homogeneousComponent p
 f) = if degree d = p then coe…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
（共 50 条，此处仅展示前 30 条）
-/
theorem truncTotal_subst_eq_truncTotal_subst_sum (ha : HasSubst a)
    (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      ((∑ i ∈ range k, (f.homogeneousComponent i)).subst a).truncTotal k := by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    have h1 := coeff_subst_finite ha f d
    have h2 := coeff_subst_finite ha (∑ i ∈ range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1, finsum_eq_sum _ h2]
    have : h2.toFinset ⊆ h1.toFinset := by simp +contextual [coeff_homogeneousComponent]
    have aux {n : σ →₀ ℕ} : coeff d (n.prod fun s e ↦ a s ^ e) ≠ 0 → n.degree ≤ d.degree := by
      contrapose!
      intro hc
      rw [Finsupp.prod]
      refine coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr hc)
        (.trans ?_ (le_order_prod _ n.support)))
      exact_mod_cast sum_le_sum fun i hi => le_order_pow_of_constantCoeff_eq_zero _ (ha₁ i)
    rw [← Finset.sum_subset this]
    · congr! 2 with n hn
      simp only [map_sum, coeff_homogeneousComponent, sum_ite_eq, mem_range, left_eq_ite_iff,
        not_lt]
      have : n.degree ≤ d.degree := by
        simp only [map_sum, Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hn
        exact aux (right_ne_zero_of_smul hn)
      grind
    · simp +contextual only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, map_sum,
        coeff_homogeneousComponent, sum_ite_eq, mem_range, ite_smul, zero_smul, ite_eq_right_iff,
        imp_false, not_lt, not_le]
      grind [right_ne_zero_of_smul]
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_sum_subst (ha : HasSubst a) (ha₁ : forall i
, (a i).constantCoeff = 0) : truncTotal k (f.subst a) = (∑ i in range k, (f.homo
geneousComponent i).subst a).truncTotal k
参数：ha : HasSubst a；ha₁ : forall i, (a i).constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum`：truncTotal_subst
_eq_truncTotal_subst_sum (ha : HasSubst a) (ha₁ : forall i, (a i).constantCoeff 
= 0) : truncTotal k (f.subst a) = ((∑ i in r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst (ha : HasSubst a)
    (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      (∑ i ∈ range k, (f.homogeneousComponent i).subst a).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_sum ha ha₁, ← substAlgHom_apply ha, map_sum]
  simp
/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst** 是 Mathlib 中的一个
定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_truncTotal_subst [Finite σ] (h : forall i, 
(a i).constantCoeff = 0) : truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowe
rSeries.subst a).truncTotal k
参数：h : forall i, (a i).constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum`：truncTotal_subst
_eq_truncTotal_subst_sum (ha : HasSubst a) (ha₁ : forall i, (a i).constantCoeff 
= 0) : truncTotal k (f.subst a) = ((∑ i in r…
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `MvPowerSeries.truncTotal_eq_sum`：truncTotal_eq_sum : p.truncTotal n = ∑ 
i in range n, p.homogeneousComponent i
-/
theorem truncTotal_subst_eq_truncTotal_truncTotal_subst [Finite σ]
    (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst a).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_sum (hasSubst_of_constantCoeff_zero h) h,
    truncTotal_eq_sum]
/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le** 是 Ma
thlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le (ha : HasSubst a
) (h : forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i) : truncTotal
 k (f.subst a) = (∑ i in range k, (f.homogeneousComponent i).subst (fun i => ((a
 i).truncTotal (x i)).toMvPowerSeries)).truncTotal k
参数：ha : HasSubst a；h : forall i, (a i).constantCoeff = 0；hx : forall i, k <= x i
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le`：tru
ncTotal_subst_eq_truncTotal_subst_truncTotal_of_le (ha : HasSubst a) (hx : foral
l i, k <= x i) : (f.subst a).truncTotal k = (f.subst fun …
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst`：truncTotal_subst
_eq_truncTotal_sum_subst (ha : HasSubst a) (ha₁ : forall i, (a i).constantCoeff 
= 0) : truncTotal k (f.subst a) = (∑ i in ra…
· 使用定理 `MvPowerSeries.HasSubst.truncTotal`：∀ {σ : Type u_1} {τ : Type u_4} {S : 
Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {x : σ → ℕ}   [inst_1 
: Finite τ],   MvPowerS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPolynomial.coeff_coe`：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff 
n ↑φ = coeff n φ
· 使用定理 `MvPolynomial.constantCoeff_eq`：constantCoeff_eq : (constantCoeff : MvPol
ynomial σ R -> R) = coeff 0
· 使用定理 `MvPowerSeries.constantCoeff_truncTotal_eq_ite`：constantCoeff_truncTotal_
eq_ite : (truncTotal n p).constantCoeff = if 0 < n then p.constantCoeff else 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le (ha : HasSubst a)
    (h : ∀ i, (a i).constantCoeff = 0) (hx : ∀ i, k ≤ x i) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha hx]
  exact truncTotal_subst_eq_truncTotal_sum_subst ha.truncTotal fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, constantCoeff_truncTotal_eq_ite, h i, ite_self]
/-
**MvPowerSeries.truncTotal_subst_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：truncTotal_subst_of_le [Finite σ] (h : forall i, (a i).constantCoeff = 0) 
(hx : forall i, k <= x i) : truncTotal k (f.subst a) = ((f.truncTotal k).toMvPow
erSeries.subst (fun i => ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k
参数：h : forall i, (a i).constantCoeff = 0；hx : forall i, k <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le`
：truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le (ha : HasSubst a) (h 
: forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i…
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `MvPowerSeries.truncTotal_eq_sum`：truncTotal_eq_sum : p.truncTotal n = ∑ 
i in range n, p.homogeneousComponent i
· 使用定理 `MvPowerSeries.HasSubst.truncTotal`：∀ {σ : Type u_1} {τ : Type u_4} {S : 
Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {x : σ → ℕ}   [inst_1 
: Finite τ],   MvPowerS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncTotal_subst_of_le [Finite σ] (h : ∀ i, (a i).constantCoeff = 0) (hx : ∀ i, k ≤ x i) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero h) h hx,
    truncTotal_eq_sum, ← substAlgHom_apply
      (hasSubst_of_constantCoeff_zero h).truncTotal, map_sum]
  simp
/-
**MvPowerSeries.truncTotal_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst [Finite σ] (h : forall i, (a i).constantCoeff = 0) : trun
cTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst (fun i => ((a i).
truncTotal k).toMvPowerSeries)).truncTotal k
参数：h : forall i, (a i).constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncTotal_subst_of_le`：truncTotal_subst_of_le [Finite σ] 
(h : forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i) : truncTotal k
 (f.subst a) = ((f.truncTo…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem truncTotal_subst [Finite σ] (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i ↦ ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_of_le h fun _ ↦ le_refl k
/-
**MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst_truncTotal** 是 Mathlib 
中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_subst_eq_truncTotal_sum_subst_truncTotal (ha : HasSubst a) (h :
 forall i, (a i).constantCoeff = 0) : truncTotal k (f.subst a) = (∑ i in range k
, (f.homogeneousComponent i).subst (fun i => ((a i).truncTotal k).toMvPowerSerie
s)).truncTotal k
参数：ha : HasSubst a；h : forall i, (a i).constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le`
：truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le (ha : HasSubst a) (h 
: forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal (ha : HasSubst a)
    (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le ha h fun _ ↦ le_refl k

end truncTotal

section rescale

section CommSemiring

variable {R : Type*} [CommSemiring R]

-- To match the `PowerSeries.rescale` API which holds for `CommSemiring`,
-- we redo it by hand.

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism taking a multivariate power series `f(X)` to `f(aX)`. -/
/-
**MvPowerSeries.rescale** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale (a : σ -> R) : MvPowerSeries σ R ->+* MvPowerSeries σ R where toFu
n f
参数：a : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism taking a multivariate power series `f(X)` to `f(aX)`.
-/
noncomputable def rescale (a : σ → R) : MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun f := fun n ↦ (n.prod fun s m ↦ a s ^ m) * f.coeff n
  map_zero' := by
    ext
    simp [map_zero, coeff_apply]
  map_one' := by
    ext1 n
    classical
    simp only [coeff_one, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h, coeff_apply]
    · simp only [coeff_apply, ite_eq_right_iff]
      exact fun a_1 ↦ False.elim (h a_1)
  map_add' := by
    intros
    ext
    exact mul_add _ _ _
  map_mul' f g := by
    ext n
    classical
    rw [coeff_apply, coeff_mul, coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_antidiagonal] at hx
    rw [← hx]
    simp only [coeff_apply]
    rw [Finsupp.prod_of_support_subset _ Finsupp.support_add,
      Finsupp.prod_of_support_subset x.1 Finset.subset_union_left,
      Finsupp.prod_of_support_subset x.2 Finset.subset_union_right]
    · simp only [← mul_assoc]
      congr 1
      rw [mul_assoc, mul_comm (f x.1), ← mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      simp [pow_add]
    all_goals {simp}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MvPowerSeries.coeff_rescale** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_rescale (f : MvPowerSeries σ R) (a : σ -> R) (n : σ ->₀ Nat) : coeff
 n (rescale a f) = (n.prod fun s m => a s ^ m) * f.coeff n
参数：f : MvPowerSeries σ R；a : σ -> R；n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_rescale (f : MvPowerSeries σ R) (a : σ → R) (n : σ →₀ ℕ) :
    coeff n (rescale a f) = (n.prod fun s m ↦ a s ^ m) * f.coeff n := by
  simp [rescale, coeff_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MvPowerSeries.rescale_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_zero : (rescale 0 : MvPowerSeries σ R ->+* MvPowerSeries σ R) = C.
comp constantCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem rescale_zero :
    (rescale 0 : MvPowerSeries σ R →+* MvPowerSeries σ R) = C.comp constantCoeff := by
  classical
  ext x n
  simp only [rescale, Pi.zero_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    RingHom.coe_comp, Function.comp_apply, coeff_C]
  split_ifs with h
  · simp [h, coeff_apply, ← @coeff_zero_eq_constantCoeff_apply, coeff_apply]
  · simp only [coeff_apply]
    convert! zero_mul _
    simp only [DFunLike.ext_iff, not_forall, Finsupp.coe_zero, Pi.zero_apply] at h
    obtain ⟨s, h⟩ := h
    simp only [Finsupp.prod]
    apply Finset.prod_eq_zero (i := s) _ (zero_pow h)
    simpa using h
/-
**MvPowerSeries.rescale_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_zero_apply (f : MvPowerSeries σ R) : rescale 0 f = C (constantCoef
f f)
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.rescale_zero`：rescale_zero : (rescale 0 : MvPowerSeries σ 
R ->+* MvPowerSeries σ R) = C.comp constantCoeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_zero_apply (f : MvPowerSeries σ R) :
    rescale 0 f = C (constantCoeff f) := by simp

@[simp]
/-
**MvPowerSeries.rescale_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_one : rescale 1 = RingHom.id (MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_one : rescale 1 = RingHom.id (MvPowerSeries σ R) := by
  ext f n
  simp [coeff_rescale, Finsupp.prod]
/-
**MvPowerSeries.rescale_rescale** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_rescale (f : MvPowerSeries σ R) (a b : σ -> R) : rescale b (rescal
e a f) = rescale (a * b) f
参数：f : MvPowerSeries σ R；a b : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Finsupp.prod_mul`：prod_mul [Zero M] [CommMonoid N] {f : α ->₀ M} {h₁ h₂ 
: α -> M -> N} : (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_rescale (f : MvPowerSeries σ R) (a b : σ → R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp [← mul_assoc, mul_pow, mul_comm]
/-
**MvPowerSeries.rescale_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_mul (a b : σ -> R) : rescale (a * b) = (rescale b).comp (rescale a
)
参数：a b : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_mul (a b : σ → R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]

set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling a homogeneous power series -/
/-
**MvPowerSeries.rescale_homogeneous_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：rescale_homogeneous_eq_smul {n : Nat} {r : R} {f : MvPowerSeries σ R} (hf 
: forall d in f.support, d.degree = n) : MvPowerSeries.rescale (Function.const σ
 r) f = r ^ n • f
参数：hf : forall d in f.support, d.degree = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.degree_apply`：degree_apply (d : σ ->₀ R) : degree d = ∑ i in d.s
upport, d i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rescaling a homogeneous power series
-/
lemma rescale_homogeneous_eq_smul {n : ℕ} {r : R} {f : MvPowerSeries σ R}
    (hf : ∀ d ∈ f.support, d.degree = n) :
    MvPowerSeries.rescale (Function.const σ r) f = r ^ n • f := by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul, Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : e ∈ f.support
  · rw [← hf e he, Finsupp.degree_apply]
  · simp only [Function.mem_support, ne_eq, not_not] at he
    simp [he, mul_zero, coeff_apply]

/-- Rescale a multivariate power series, as a `MonoidHom` in the scaling parameters. -/
/-
**MvPowerSeries.rescaleMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：rescaleMonoidHom : (σ -> R) ->* MvPowerSeries σ R ->+* MvPowerSeries σ R w
here toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.rescale_one`：rescale_one : rescale 1 = RingHom.id (MvPower
Series σ R)

--- 原说明 ---
Rescale a multivariate power series, as a `MonoidHom` in the scaling parameters.
-/
noncomputable def rescaleMonoidHom :
    (σ → R) →* MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := rescale
  map_one' := rescale_one
  map_mul' a b := by ext; simp [mul_comm, rescale_rescale]

end CommSemiring

section CommRing

/-
**MvPowerSeries.rescale_eq_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescale_eq_subst (a : σ -> R) (f : MvPowerSeries σ R) : rescale a f = subs
t (a • X) f
参数：a : σ -> R；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.smul_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] (a : σ → R), MvPowerSeries.HasSubst (a • MvPowerSeries.X)
· 使用定理 `MvPowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (
f : MvPowerSeries σ R) (e : τ ->₀ Nat) : (fun d => coeff d f • (coeff e (d.prod 
fun s e => (a s) ^ e))…
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.monomial_eq`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommS
emiring R] (e : σ →₀ ℕ) (r : σ → R),   (MvPowerSeries.monomial e) (e.prod fun s 
n => r s ^ n) =…
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_eq_subst (a : σ → R) (f : MvPowerSeries σ R) :
    rescale a f = subst (a • X) f := by
  classical
  ext n
  rw [coeff_rescale]
  rw [coeff_subst (HasSubst.smul_X a),
    finsum_eq_sum _ (coeff_subst_finite (HasSubst.smul_X a) f n)]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [Finset.sum_eq_single n _ _]
  · simp [mul_comm, ← monomial_eq]
  · intro b hb hbn
    rw [← monomial_eq, coeff_monomial, if_neg (Ne.symm hbn), mul_zero]
  · intro hn
    simpa using hn

/-- Rescale a multivariate power series, as an `AlgHom` in the scaling parameters,
by multiplying each variable `x` by the value `a x`. -/
/-
**MvPowerSeries.rescaleAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：rescaleAlgHom (a : σ -> R) : MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R
参数：a : σ -> R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.smul_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] (a : σ → R), MvPowerSeries.HasSubst (a • MvPowerSeries.X)

--- 原说明 ---
Rescale a multivariate power series, as an `AlgHom` in the scaling parameters,
by multiplying each variable `x` by the value `a x`.
-/
noncomputable def rescaleAlgHom (a : σ → R) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.smul_X a)
/-
**MvPowerSeries.rescaleAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescaleAlgHom_apply (a : σ -> R) (f : MvPowerSeries σ R) : rescaleAlgHom a
 f = rescale a f
参数：a : σ -> R；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.smul_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] (a : σ → R), MvPowerSeries.HasSubst (a • MvPowerSeries.X)
· 使用定理 `MvPowerSeries.rescale_eq_subst`：rescale_eq_subst (a : σ -> R) (f : MvPow
erSeries σ R) : rescale a f = subst (a • X) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescaleAlgHom_apply (a : σ → R) (f : MvPowerSeries σ R) :
    rescaleAlgHom a f = rescale a f := by
  simp [rescaleAlgHom, rescale_eq_subst]
/-
**MvPowerSeries.rescaleAlgHom_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescaleAlgHom_mul (a b : σ -> R) : rescaleAlgHom (a * b) = (rescaleAlgHom 
b).comp (rescaleAlgHom a)
参数：a b : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.rescaleAlgHom_apply`：rescaleAlgHom_apply (a : σ -> R) (f :
 MvPowerSeries σ R) : rescaleAlgHom a f = rescale a f
· 使用定理 `MvPowerSeries.rescale_rescale`：rescale_rescale (f : MvPowerSeries σ R) (
a b : σ -> R) : rescale b (rescale a f) = rescale (a * b) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescaleAlgHom_mul (a b : σ → R) :
    rescaleAlgHom (a * b) = (rescaleAlgHom b).comp (rescaleAlgHom a) := by
  ext1 f
  simp [rescaleAlgHom_apply, rescale_rescale]
/-
**MvPowerSeries.rescaleAlgHom_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rescaleAlgHom_one : rescaleAlgHom 1 = AlgHom.id R (MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.HasSubst.smul_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] (a : σ → R), MvPowerSeries.HasSubst (a • MvPowerSeries.X)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MvPowerSeries.substAlgHom.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [i
nst : CommRing R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   [inst_2 
: Algebra R S] {a a_1 : σ …
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.subst_self`：subst_self : subst (MvPowerSeries.X : σ -> MvP
owerSeries σ R) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescaleAlgHom_one :
    rescaleAlgHom 1 = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 f
  simp [rescaleAlgHom, subst_self]

end CommRing

end rescale

section

variable {x : ℕ → MvPowerSeries σ R}
  [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/-
**MvPowerSeries.subst_tsum** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：subst_tsum (hx : Summable x) (ha : HasSubst a) : (∑' i, x i).subst a = ∑' 
i, ((x i).subst a)
参数：hx : Summable x；ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…
· 使用定理 `Summable.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFil
ter β} …
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPowerSeries.continuous_aeval`：continuous_aeval (ha : HasEval a) : Cont
inuous (aeval ha : MvPowerSeries σ R -> S)
-/
lemma subst_tsum (hx : Summable x) (ha : HasSubst a) :
    (∑' i, x i).subst a = ∑' i, ((x i).subst a) := by
  rw [← coe_substAlgHom ha, substAlgHom_eq_aeval ha, hx.map_tsum _ <| continuous_aeval _]
/-
**MvPowerSeries.summable_subst** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：summable_subst (hx : Summable x) (ha : HasSubst a) : Summable fun i => (x 
i).subst a
参数：hx : Summable x；ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…
· 使用定理 `Summable.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β
} …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPowerSeries.continuous_aeval`：continuous_aeval (ha : HasEval a) : Cont
inuous (aeval ha : MvPowerSeries σ R -> S)
-/
lemma summable_subst (hx : Summable x) (ha : HasSubst a) :
    Summable fun i => (x i).subst a := by
  rw [← coe_substAlgHom ha, substAlgHom_eq_aeval ha]
  exact hx.map _ <| continuous_aeval ha.hasEval

end

end MvPowerSeries

