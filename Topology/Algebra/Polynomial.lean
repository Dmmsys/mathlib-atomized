/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `Polynomial.continuous_eval₂`: `Polynomial.eval₂` defines a continuous function.
* `Polynomial.continuous_aeval`: `Polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `Polynomial.continuousAt_aeval`,
  `Polynomial.continuousWithinAt_aeval`, `Polynomial.continuousOn_aeval`.
* `Polynomial.continuous`:  `Polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `Polynomial.continuousAt`, `Polynomial.continuousWithinAt`,
  `Polynomial.continuousOn`.
* `Polynomial.tendsto_norm_atTop`: `fun x ↦ ‖Polynomial.eval (z x) p‖` tends to infinity provided
  that `fun x ↦ ‖z x‖` tends to infinity and `0 < degree p`;
* `Polynomial.tendsto_abv_eval₂_atTop`, `Polynomial.tendsto_abv_atTop`,
  `Polynomial.tendsto_abv_aeval_atTop`: a few versions of the previous statement for
  `IsAbsoluteValue abv` instead of norm.

## Tags

Polynomial, continuity
-/

public section


open IsAbsoluteValue Filter

namespace Polynomial

section IsTopologicalSemiring

variable {R S : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] (p : R[X])

@[continuity, fun_prop]
/-
**Polynomial.continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem continuous_eval₂ [Semiring S] (p : S[X]) (f : S →+* R) :
    Continuous fun x => p.eval₂ f x := by
  simp only [eval₂_eq_sum]
  exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_pow _)

@[continuity, fun_prop]
/-
**Polynomial.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : TopologicalSpace R] [IsTopo
logicalSemiring R] (p : Polynomial R),   Continuous fun x => Polynomial.eval x p
参数：p : Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.continuous_eval₂`：∀ {R : Type u_1} {S : Type u_2} [inst : Sem
iring R] [inst_1 : TopologicalSpace R] [IsTopologicalSemiring R]   [inst_3 : Sem
iring S] (p : Pol…
-/
protected theorem continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _

@[fun_prop]
/-
**Polynomial.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : TopologicalSpace R] [IsTopo
logicalSemiring R] (p : Polynomial R) {a : R},   ContinuousAt (fun x => Polynomi
al.eval x p) a
参数：p : Polynomial R；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
-/
protected theorem continuousAt {a : R} : ContinuousAt (fun x => p.eval x) a :=
  p.continuous.continuousAt

@[fun_prop]
/-
**Polynomial.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : TopologicalSpace R] [IsTopo
logicalSemiring R] (p : Polynomial R)   {s : Set R} {a : R}, ContinuousWithinAt 
(fun x => Polynomial.eval x p) s a
参数：p : Polynomial R；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
-/
protected theorem continuousWithinAt {s a} : ContinuousWithinAt (fun x => p.eval x) s a :=
  p.continuous.continuousWithinAt

@[fun_prop]
/-
**Polynomial.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : TopologicalSpace R] [IsTopo
logicalSemiring R] (p : Polynomial R)   {s : Set R}, ContinuousOn (fun x => Poly
nomial.eval x p) s
参数：p : Polynomial R；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
-/
protected theorem continuousOn {s} : ContinuousOn (fun x => p.eval x) s :=
  p.continuous.continuousOn

end IsTopologicalSemiring

section TopologicalAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A] (p : R[X])

@[continuity, fun_prop]
/-
**Polynomial.continuous_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   [inst_3 : TopologicalSpace A] [IsTopologicalSemirin
g A] (p : Polynomial R), Continuous fun x => (Polynomial.aeval x) p
参数：p : Polynomial R；Polynomial.aeval x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.continuous_eval₂`：∀ {R : Type u_1} {S : Type u_2} [inst : Sem
iring R] [inst_1 : TopologicalSpace R] [IsTopologicalSemiring R]   [inst_3 : Sem
iring S] (p : Pol…
-/
protected theorem continuous_aeval : Continuous fun x : A => aeval x p :=
  p.continuous_eval₂ _

@[fun_prop]
/-
**Polynomial.continuousAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   [inst_3 : TopologicalSpace A] [IsTopologicalSemirin
g A] (p : Polynomial R) {a : A},   ContinuousAt (fun x => (Polynomial.aeval x) p
) a
参数：p : Polynomial R；fun x => (Polynomial.aeval x) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Polynomial.continuous_aeval`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Topologica
lSpace A] [IsTopo…
-/
protected theorem continuousAt_aeval {a : A} : ContinuousAt (fun x : A => aeval x p) a :=
  p.continuous_aeval.continuousAt

@[fun_prop]
/-
**Polynomial.continuousWithinAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   [inst_3 : TopologicalSpace A] [IsTopologicalSemirin
g A] (p : Polynomial R) {s : Set A} {a : A},   ContinuousWithinAt (fun x => (Pol
ynomial.aeval x) p) s a
参数：p : Polynomial R；fun x => (Polynomial.aeval x) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Polynomial.continuous_aeval`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Topologica
lSpace A] [IsTopo…
-/
protected theorem continuousWithinAt_aeval {s a} :
    ContinuousWithinAt (fun x : A => aeval x p) s a :=
  p.continuous_aeval.continuousWithinAt

@[fun_prop]
/-
**Polynomial.continuousOn_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   [inst_3 : TopologicalSpace A] [IsTopologicalSemirin
g A] (p : Polynomial R) {s : Set A},   ContinuousOn (fun x => (Polynomial.aeval 
x) p) s
参数：p : Polynomial R；fun x => (Polynomial.aeval x) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Polynomial.continuous_aeval`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Topologica
lSpace A] [IsTopo…
-/
protected theorem continuousOn_aeval {s} : ContinuousOn (fun x : A => aeval x p) s :=
  p.continuous_aeval.continuousOn

end TopologicalAlgebra

/-
**Polynomial.tendsto_abv_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_abv_eval₂_atTop {R S k α : Type*} [Semiring R] [Ring S]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : R →+* S) (abv : S → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (hf : f p.leadingCoeff ≠ 0) {l : Filter α} {z : α → S} (hz : Tendsto (abv ∘ z) l atTop) :
    Tendsto (fun x => abv (p.eval₂ f (z x))) l atTop := by
  revert hf; refine degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [leadingCoeff_mul_X, leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] using (ihp hf).atTop_mul_atTop₀ hz
  · intro _ a hd ihp hf
    rw [add_comm, leadingCoeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf
    refine .atTop_of_add_const (abv (-f a)) ?_
    refine tendsto_atTop_mono (fun _ => abv_add abv _ _) ?_
    simpa using ihp hf
/-
**Polynomial.tendsto_abv_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：tendsto_abv_atTop {R k α : Type*} [Ring R] [Field k] [LinearOrder k] [IsSt
rictOrderedRing k] (abv : R -> k) [IsAbsoluteValue abv] (p : R[X]) (h : 0 < degr
ee p) {l : Filter α} {z : α -> R} (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fu
n x => abv (p.eval (z x))) l atTop
参数：abv : R -> k；p : R[X]；h : 0 < degree p；hz : Tendsto (abv ∘ z) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.tendsto_abv_eval₂_atTop`：tendsto_abv_eval₂_atTop {R S k α : T
ype*} [Semiring R] [Ring S] [Field k] [LinearOrder k] [IsStrictOrderedRing k] (f
 : R ->+* S) (abv : S ->…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
-/
theorem tendsto_abv_atTop {R k α : Type*} [Ring R]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k] (abv : R → k)
    [IsAbsoluteValue abv] (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (p.eval (z x))) l atTop := by
  apply tendsto_abv_eval₂_atTop _ _ _ h _ hz
  exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)
/-
**Polynomial.tendsto_abv_aeval_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：tendsto_abv_aeval_atTop {R A k α : Type*} [CommSemiring R] [Ring A] [Algeb
ra R A] [Field k] [LinearOrder k] [IsStrictOrderedRing k] (abv : A -> k) [IsAbso
luteValue abv] (p : R[X]) (hd : 0 < degree p) (h₀ : algebraMap R A p.leadingCoef
f != 0) {l : Filter α} {z : α -> A} (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (
fun x => abv (aeval (z x) p)) l atTop
参数：abv : A -> k；p : R[X]；hd : 0 < degree p；h₀ : algebraMap R A p.leadingCoeff !=
 0；hz : Tendsto (abv ∘ z) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.tendsto_abv_eval₂_atTop`：tendsto_abv_eval₂_atTop {R S k α : T
ype*} [Semiring R] [Ring S] [Field k] [LinearOrder k] [IsStrictOrderedRing k] (f
 : R ->+* S) (abv : S ->…
-/
theorem tendsto_abv_aeval_atTop {R A k α : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (abv : A → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (h₀ : algebraMap R A p.leadingCoeff ≠ 0) {l : Filter α} {z : α → A}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (aeval (z x) p)) l atTop :=
  tendsto_abv_eval₂_atTop _ abv p hd h₀ hz

variable {α R : Type*} [NormedRing R] [IsAbsoluteValue (norm : R → ℝ)]
/-
**Polynomial.tendsto_norm_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：tendsto_norm_atTop (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α -> 
R} (hz : Tendsto (fun x => ‖z x‖) l atTop) : Tendsto (fun x => ‖p.eval (z x)‖) l
 atTop
参数：p : R[X]；h : 0 < degree p；hz : Tendsto (fun x => ‖z x‖) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.tendsto_abv_atTop`：tendsto_abv_atTop {R k α : Type*} [Ring R]
 [Field k] [LinearOrder k] [IsStrictOrderedRing k] (abv : R -> k) [IsAbsoluteVal
ue abv] (p : R[X])…
-/
theorem tendsto_norm_atTop (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) : Tendsto (fun x => ‖p.eval (z x)‖) l atTop :=
  p.tendsto_abv_atTop norm h hz
/-
**Polynomial.exists_forall_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_forall_norm_le [ProperSpace R] (p : R[X]) : exists x, forall y, ‖p.
eval x‖ <= ‖p.eval y‖
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le`：Continuous.exists_forall_le [ClosedIicTopol
ogy α] [Nonempty β] {f : β -> α} (hf : Continuous f) (hlim : Tendsto f (cocompac
t β) atTop) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Polynomial.tendsto_norm_atTop`：tendsto_norm_atTop (p : R[X]) (h : 0 < de
gree p) {l : Filter α} {z : α -> R} (hz : Tendsto (fun x => ‖z x‖) l atTop) : Te
ndsto (fun x => ‖p.…
· 使用定理 `tendsto_norm_cocompact_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] [ProperSpace E], Filter.Tendsto norm (Filter.cocompact E) Filter.atTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem exists_forall_norm_le [ProperSpace R] (p : R[X]) : ∃ x, ∀ y, ‖p.eval x‖ ≤ ‖p.eval y‖ :=
  if hp0 : 0 < degree p then
    p.continuous.norm.exists_forall_le <| p.tendsto_norm_atTop hp0 tendsto_norm_cocompact_atTop
  else
    ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩
/-
**Polynomial.isProperMap_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isProperMap_eval [ProperSpace R] (p : R[X]) (h : 0 < degree p) : IsProperM
ap p.eval
参数：p : R[X]；h : 0 < degree p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isProperMap_iff_tendsto_cocompact`：isProperMap_iff_tendsto_cocompact : I
sProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用定理 `Polynomial.tendsto_norm_atTop`：tendsto_norm_atTop (p : R[X]) (h : 0 < de
gree p) {l : Filter α} {z : α -> R} (hz : Tendsto (fun x => ‖z x‖) l atTop) : Te
ndsto (fun x => ‖p.…
· 使用定理 `tendsto_norm_cobounded_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto norm (Bornology.cobounded E) Filter.atTop
-/
theorem isProperMap_eval [ProperSpace R] (p : R[X]) (h : 0 < degree p) : IsProperMap p.eval :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨by fun_prop, by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact p.tendsto_norm_atTop h tendsto_norm_cobounded_atTop⟩
/-
**Polynomial.isClosedMap_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isClosedMap_eval [ProperSpace R] (p : R[X]) : IsClosedMap p.eval
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_le_zero_iff`：degree_le_zero_iff : degree p <= 0 ↔ p = 
C (coeff p 0)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `isClosedMap_const`：isClosedMap_const {X Y} [TopologicalSpace X] [Topolog
icalSpace Y] [T1Space Y] {y : Y} : IsClosedMap (Function.const X y)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `Polynomial.isProperMap_eval`：isProperMap_eval [ProperSpace R] (p : R[X])
 (h : 0 < degree p) : IsProperMap p.eval
-/
theorem isClosedMap_eval [ProperSpace R] (p : R[X]) : IsClosedMap p.eval := by
  obtain h | h := le_or_gt p.degree 0
  · rw [degree_le_zero_iff.mp h]; simpa using! isClosedMap_const
  · exact (p.isProperMap_eval h).isClosedMap

variable (R) in
/-
**Polynomial._root_.isClosedMap_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isClosedMap_pow [ProperSpace R] (n : ℕ) : IsClosedMap fun x : R ↦ x ^ n := by
  simpa [eval_X_pow] using (X ^ n).isClosedMap_eval

section Roots

open Polynomial NNReal

variable {F K : Type*} [CommRing F] [NormedField K]

open Multiset

/-
**Polynomial.eq_one_of_roots_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_one_of_roots_le {p : F[X]} {f : F ->+* K} {B : Real} (hB : B < 0) (h1 :
 p.Monic) (h2 : Splits (p.map f)) (h3 : forall z in (map f p).roots, ‖z‖ <= B) :
 p = 1
参数：hB : B < 0；h1 : p.Monic；h2 : Splits (p.map f)；h3 : forall z in (map f p).root
s, ‖z‖ <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.card_pos_iff_exists_mem`：card_pos_iff_exists_mem {s : Multiset 
α} : 0 < card s ↔ exists a, a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem eq_one_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (hB : B < 0) (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) : p = 1 :=
  h1.natDegree_eq_zero.mp (by
    contrapose! hB
    rw [← h1.natDegree_map f, Splits.natDegree_eq_card_roots h2] at hB
    obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB)
    exact le_trans (norm_nonneg _) (h3 z hz))
/-
**Polynomial.coeff_le_of_roots_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_le_of_roots_le {p : F[X]} {f : F ->+* K} {B : Real} (i : Nat) (h1 : 
p.Monic) (h2 : Splits (p.map f)) (h3 : forall z in (map f p).roots, ‖z‖ <= B) : 
‖(map f p).coeff i‖ <= B ^ (p.natDegree - i) * p.natDegree.choose i
参数：i : Nat；h1 : p.Monic；h2 : Splits (p.map f)；h3 : forall z in (map f p).roots, 
‖z‖ <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_one_of_roots_le`：eq_one_of_roots_le {p : F[X]} {f : F ->+*
 K} {B : Real} (hB : B < 0) (h1 : p.Monic) (h2 : Splits (p.map f)) (h3 : forall 
z in (map f p).root…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
（共 67 条，此处仅展示前 30 条）
-/
theorem coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ) (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) :
    ‖(map f p).coeff i‖ ≤ B ^ (p.natDegree - i) * p.natDegree.choose i := by
  obtain hB | hB := lt_or_ge B 0
  · rw [eq_one_of_roots_le hB h1 h2 h3, Polynomial.map_one, natDegree_one, zero_tsub, pow_zero,
      one_mul, coeff_one]
    split_ifs with h <;> simp [h]
  rw [← h1.natDegree_map f]
  obtain hi | hi := lt_or_ge (map f p).natDegree i
  · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
    positivity
  rw [coeff_eq_esymm_roots_of_splits h2 hi, (h1.map _).leadingCoeff,
    one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  apply ((norm_multiset_sum_le _).trans <| sum_le_card_nsmul _ _ fun r hr => _).trans
  · rw [Multiset.map_map, card_map, card_powersetCard, ← Splits.natDegree_eq_card_roots h2,
      Nat.choose_symm hi, mul_comm, nsmul_eq_mul]
  intro r hr
  simp_rw [Multiset.mem_map] at hr
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hr
  rw [mem_powersetCard] at hs
  lift B to ℝ≥0 using hB
  rw [← coe_nnnorm, ← NNReal.coe_pow, NNReal.coe_le_coe, ← nnnormHom_apply, ← MonoidHom.coe_coe,
    MonoidHom.map_multiset_prod]
  refine (prod_le_pow_card _ B fun x hx => ?_).trans_eq (by rw [card_map, hs.2])
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
  exact h3 z (mem_of_le hs.1 hz)

/-- The coefficients of the monic polynomials of bounded degree with bounded roots are
uniformly bounded. -/
/-
**Polynomial.coeff_bdd_of_roots_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_bdd_of_roots_le {B : Real} {d : Nat} (f : F ->+* K) {p : F[X]} (h1 :
 p.Monic) (h2 : Splits (p.map f)) (h3 : p.natDegree <= d) (h4 : forall z in (map
 f p).roots, ‖z‖ <= B) (i : Nat) : ‖(map f p).coeff i‖ <= max B 1 ^ d * d.choose
 (d / 2)
参数：f : F ->+* K；h1 : p.Monic；h2 : Splits (p.map f)；h3 : p.natDegree <= d；h4 : fo
rall z in (map f p).roots, ‖z‖ <= B；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.coeff_le_of_roots_le`：coeff_le_of_roots_le {p : F[X]} {f : F 
->+* K} {B : Real} (i : Nat) (h1 : p.Monic) (h2 : Splits (p.map f)) (h3 : forall
 z in (map f p).roots…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Nat.choose_mono`：choose_mono (b : Nat) : Monotone fun a => choose a b
· 使用定理 `Nat.choose_le_middle`：choose_le_middle (r n : Nat) : choose n r <= choos
e n (n / 2)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_one_of_roots_le`：eq_one_of_roots_le {p : F[X]} {f : F ->+*
 K} {B : Real} (hB : B < 0) (h1 : p.Monic) (h2 : Splits (p.map f)) (h3 : forall 
z in (map f p).root…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The coefficients of the monic polynomials of bounded degree with bounded roots a
re
uniformly bounded.
-/
theorem coeff_bdd_of_roots_le {B : ℝ} {d : ℕ} (f : F →+* K) {p : F[X]} (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : p.natDegree ≤ d) (h4 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) (i : ℕ) :
    ‖(map f p).coeff i‖ ≤ max B 1 ^ d * d.choose (d / 2) := by
  obtain hB | hB := le_or_gt 0 B
  · apply (coeff_le_of_roots_le i h1 h2 h4).trans
    calc
      _ ≤ max B 1 ^ (p.natDegree - i) * p.natDegree.choose i := by gcongr; apply le_max_left
      _ ≤ max B 1 ^ d * p.natDegree.choose i := by
        gcongr
        · apply le_max_right
        · exact le_trans (Nat.sub_le _ _) h3
      _ ≤ max B 1 ^ d * d.choose (d / 2) := by
        gcongr; exact (i.choose_mono h3).trans (i.choose_le_middle d)
  · rw [eq_one_of_roots_le hB h1 h2 h4, Polynomial.map_one, coeff_one]
    refine le_trans ?_ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right B 1)) ?_)
    · split_ifs <;> norm_num
    · exact mod_cast Nat.succ_le_iff.mpr (Nat.choose_pos (d.div_le_self 2))

end Roots

end Polynomial

