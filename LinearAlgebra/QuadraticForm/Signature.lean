/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Signature of a quadratic form

We define the signature of a quadratic form over a linearly ordered field, and show that it can be
computed from any sum-of-squares representation.

## Main results and definitions

* `QuadraticForm.sigPos`, `QuadraticForm.sigNeg`: for a quadratic form `Q`, the maximal dimension
  of a subspace on which `Q` is positive-definite (resp. negative-definite).
* `QuadraticForm.sigPos_of_equiv_weightedSumOfSquares`,
  `QuadraticForm.sigNeg_of_equiv_weightedSumOfSquares`: for any isomorphism from `Q` to a
  weighted sum of squares, `Q.sigPos` and `Q.sigNeg` are the number of positive and negative
  weights. (This is the uniqueness part of **Sylvester's law of inertia**; the existence is
  `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` in file
  `Mathlib.LinearAlgebra.QuadraticForm.Real`.)

## Acknowledgements

This file is based on work carried out by Sina Keller, Philipp Schumann, and Nicolas Trutmann in
the course of their studies at ETH Zürich.
-/

open Finset QuadraticMap

public noncomputable section

variable {R M M' : Type*} [AddCommGroup M] [AddCommGroup M']

section LinearOrder

variable [CommRing R] [LinearOrder R] [Module R M] (Q : QuadraticForm R M)
  [Module R M'] {Q' : QuadraticForm R M'} {V : Submodule R M}

section Equiv
variable {Q}

/-
**QuadraticMap.IsometryEquiv.map_posDef_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quadratic
Map.IsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M' : Type u_3} [inst : AddCommGroup M] [i
nst_1 : AddCommGroup M'] [inst_2 : CommRing R]   [inst_3 : LinearOrder R] [inst_
4 : _root_.Module R M] {Q : QuadraticForm R M} [inst_5 : _root_.Module R M']   {
Q' : QuadraticForm R M'} {V : Submodule R M} (e : QuadraticMap.IsometryEquiv Q Q
'),   (QuadraticMap.restrict Q' (Submodule.map (↑e.toLinearEquiv) V)).PosDef ↔ (
QuadraticMap.restrict Q V).PosDef
参数：e : QuadraticMap.IsometryEquiv Q Q'；QuadraticMap.restrict Q' (Submodule.map (
↑e.toLinearEquiv) V)；QuadraticMap.restrict Q V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `QuadraticMap.restrict_apply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : A…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
· 使用定理 `QuadraticMap.IsometryEquiv.instLinearEquivClass`：∀ {R : Type u_2} {M₁ : 
Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M₁]   [inst_2 : AddCommMonoi…
· 使用定理 `QuadraticMap.IsometryEquiv.map_app`：map_app (f : Q₁.IsometryEquiv Q₂) (m
 : M₁) : Q₂ (f m) = Q₁ m
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma QuadraticMap.IsometryEquiv.map_posDef_iff (e : IsometryEquiv Q Q') :
    (Q'.restrict (V.map e.toLinearMap)).PosDef ↔ (Q.restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]
/-
**QuadraticMap.IsometryEquiv.map_negDef_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quadratic
Map.IsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M' : Type u_3} [inst : AddCommGroup M] [i
nst_1 : AddCommGroup M'] [inst_2 : CommRing R]   [inst_3 : LinearOrder R] [inst_
4 : _root_.Module R M] {Q : QuadraticForm R M} [inst_5 : _root_.Module R M']   {
Q' : QuadraticForm R M'} {V : Submodule R M} (e : QuadraticMap.IsometryEquiv Q Q
'),   (QuadraticMap.restrict (-Q') (Submodule.map (↑e.toLinearEquiv) V)).PosDef 
↔ (QuadraticMap.restrict (-Q) V).PosDef
参数：e : QuadraticMap.IsometryEquiv Q Q'；QuadraticMap.restrict (-Q') (Submodule.ma
p (↑e.toLinearEquiv) V)；QuadraticMap.restrict (-Q) V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `QuadraticMap.restrict_apply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : A…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
· 使用定理 `QuadraticMap.IsometryEquiv.instLinearEquivClass`：∀ {R : Type u_2} {M₁ : 
Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M₁]   [inst_2 : AddCommMonoi…
· 使用定理 `QuadraticMap.IsometryEquiv.map_app`：map_app (f : Q₁.IsometryEquiv Q₂) (m
 : M₁) : Q₂ (f m) = Q₁ m
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma QuadraticMap.IsometryEquiv.map_negDef_iff (e : IsometryEquiv Q Q') :
    ((-Q').restrict (V.map e.toLinearMap)).PosDef ↔ ((-Q).restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]

end Equiv

open scoped Classical in
/-- For quadratic forms on finite-dimensional spaces, the maximal finrank of a positive-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional). -/
/-
Note the proof of nonemptiness needed for `max'` is a little fiddly since we are not assuming
`Nontrivial R`, and the `⊥` submodule of a module over the zero ring has finrank 1, not 0.
-/
/-
**sigPos** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigPos : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1

--- 原说明 ---
Note the proof of nonemptiness needed for `max'` is a little fiddly since we are
 not assuming
`Nontrivial R`, and the `⊥` submodule of a module over the zero ring has finrank
 1, not 0.
-/
def sigPos : ℕ := max' {r ∈ Iic (Module.finrank R M) |
    ∃ V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨Module.finrank R (⊥ : Submodule R M), by
    simp only [mem_filter, mem_Iic]
    refine ⟨?_, ⟨⊥, rfl, fun x hx' ↦ (hx' <| Subsingleton.elim x 0).elim⟩⟩
    nontriviality R
    simp [finrank_bot]⟩
/-
**sigPos_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigPos_le_finrank : sigPos Q <= Module.finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
lemma sigPos_le_finrank : sigPos Q ≤ Module.finrank R M := by
  classical
  exact mem_Iic.mp <| mem_of_mem_filter _ <| max'_mem _ _

/-- Defining property of `sigPos`. -/
/-
**sigPos_isGreatest** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigPos_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
 {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef} 
(sigPos Q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M

--- 原说明 ---
Defining property of `sigPos`.
-/
lemma sigPos_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | ∃ V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef} (sigPos Q) := by
  classical
  refine ⟨(mem_filter.mp <| max'_mem _ _).2, ?_⟩
  rintro _ ⟨V, rfl, hV⟩
  apply le_max'
  rw [mem_filter, mem_Iic]
  exact ⟨V.finrank_le, V, rfl, hV⟩
/-
**exists_finrank_eq_sigPos_and_posDef** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_finrank_eq_sigPos_and_posDef [Module.Finite R M] [StrongRankConditi
on R] : exists V : Submodule R M, Module.finrank R V = sigPos Q ∧ (Q.restrict V)
.PosDef
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `sigPos_isGreatest`：sigPos_isGreatest [Module.Finite R M] [StrongRankCond
ition R] : IsGreatest {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q
.restri…
-/
lemma exists_finrank_eq_sigPos_and_posDef [Module.Finite R M] [StrongRankCondition R] :
    ∃ V : Submodule R M, Module.finrank R V = sigPos Q ∧ (Q.restrict V).PosDef :=
  (sigPos_isGreatest Q).1
/-
**le_sigPos_of_posDef** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_sigPos_of_posDef [Module.Finite R M] [StrongRankCondition R] {V : Submo
dule R M} (hV : (Q.restrict V).PosDef) : Module.finrank R V <= sigPos Q
参数：hV : (Q.restrict V).PosDef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `sigPos_isGreatest`：sigPos_isGreatest [Module.Finite R M] [StrongRankCond
ition R] : IsGreatest {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q
.restri…
-/
lemma le_sigPos_of_posDef [Module.Finite R M] [StrongRankCondition R]
    {V : Submodule R M} (hV : (Q.restrict V).PosDef) :
    Module.finrank R V ≤ sigPos Q :=
  (sigPos_isGreatest Q).2 ⟨V, by tauto⟩

/-- For quadratic forms on finite-dimensional spaces, the maximal finrank of a negative-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional). -/
/-
**sigNeg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigNeg : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For quadratic forms on finite-dimensional spaces, the maximal finrank of a negat
ive-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional).
-/
def sigNeg : ℕ := sigPos (-Q)

/-- Defining property of `sigNeg`. -/
/-
**sigNeg_isGreatest** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigNeg_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
 {r | exists V : Submodule R M, Module.finrank R V = r ∧ ((-Q).restrict V).PosDe
f} (sigNeg Q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sigPos_isGreatest`：sigPos_isGreatest [Module.Finite R M] [StrongRankCond
ition R] : IsGreatest {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q
.restri…

--- 原说明 ---
Defining property of `sigNeg`.
-/
lemma sigNeg_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | ∃ V : Submodule R M, Module.finrank R V = r ∧ ((-Q).restrict V).PosDef} (sigNeg Q) :=
  sigPos_isGreatest (-Q)
/-
**exists_finrank_eq_sigNeg_and_negDef** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_finrank_eq_sigNeg_and_negDef [Module.Finite R M] [StrongRankConditi
on R] : exists V : Submodule R M, Module.finrank R V = sigNeg Q ∧ ((-Q).restrict
 V).PosDef
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finrank_eq_sigPos_and_posDef`：exists_finrank_eq_sigPos_and_posDef
 [Module.Finite R M] [StrongRankCondition R] : exists V : Submodule R M, Module.
finrank R V = sigPos Q ∧ …
-/
lemma exists_finrank_eq_sigNeg_and_negDef [Module.Finite R M] [StrongRankCondition R] :
    ∃ V : Submodule R M, Module.finrank R V = sigNeg Q ∧ ((-Q).restrict V).PosDef :=
  exists_finrank_eq_sigPos_and_posDef (-Q)
/-
**le_sigNeg_of_negDef** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_sigNeg_of_negDef [Module.Finite R M] [StrongRankCondition R] {V : Submo
dule R M} (hV : ((-Q).restrict V).PosDef) : Module.finrank R V <= sigNeg Q
参数：hV : ((-Q).restrict V).PosDef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_sigPos_of_posDef`：le_sigPos_of_posDef [Module.Finite R M] [StrongRank
Condition R] {V : Submodule R M} (hV : (Q.restrict V).PosDef) : Module.finrank R
 V <= sig…
-/
lemma le_sigNeg_of_negDef [Module.Finite R M] [StrongRankCondition R]
    {V : Submodule R M} (hV : ((-Q).restrict V).PosDef) :
    Module.finrank R V ≤ sigNeg Q :=
  le_sigPos_of_posDef (-Q) hV

variable {Q}
/-
**sigPos_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : AddCommGroup M] [inst_1 : CommRing
 R] [inst_2 : LinearOrder R]   [inst_3 : _root_.Module R M] {Q : QuadraticForm R
 M}, sigPos (-Q) = sigNeg Q
参数：-Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sigPos_neg : sigPos (-Q) = sigNeg Q := by rfl -- `by` needed since def not exposed
/-
**sigNeg_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : AddCommGroup M] [inst_1 : CommRing
 R] [inst_2 : LinearOrder R]   [inst_3 : _root_.Module R M] {Q : QuadraticForm R
 M}, sigNeg (-Q) = sigPos Q
参数：-Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sigPos_neg`：∀ {R : Type u_1} {M : Type u_2} [inst : AddCommGroup M] [ins
t_1 : CommRing R] [inst_2 : LinearOrder R]   [inst_3 : _root_.Module R M] {Q : Q
…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma sigNeg_neg : sigNeg (-Q) = sigPos Q := by rw [← sigPos_neg, neg_neg]

set_option backward.isDefEq.respectTransparency false in
/-
**QuadraticMap.Equivalent.sigPos_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuadraticMap.Equivalent.sigPos_eq (h : Equivalent Q Q') : sigPos Q = sigPo
s Q'
参数：h : Equivalent Q Q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_eq_cancel_right`：∀ {α : Sort u_1} {a b : α}, (∀ {c : α}, a = c ↔ 
b = c) ↔ a = b
· 使用定理 `LinearEquiv.finrank_map_eq`：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodul
e R M) : finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `QuadraticMap.IsometryEquiv.map_posDef_iff`：∀ {R : Type u_1} {M : Type u_
2} {M' : Type u_3} [inst : AddCommGroup M] [inst_1 : AddCommGroup M'] [inst_2 : 
CommRing R]   [inst_3 : LinearO…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma QuadraticMap.Equivalent.sigPos_eq (h : Equivalent Q Q') : sigPos Q = sigPos Q' := by
  obtain ⟨e⟩ := h
  unfold sigPos
  congr! with j
  · apply (Submodule.orderIsoMapComap e.toLinearEquiv).exists_congr
    intro V
    refine .and ?_ (IsometryEquiv.map_posDef_iff _).symm
    revert j
    rw [eq_iff_eq_cancel_right]
    exact (e.finrank_map_eq _).symm
  · exact e.toLinearEquiv.finrank_eq
/-
**QuadraticMap.Equivalent.sigNeg_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuadraticMap.Equivalent.sigNeg_eq (h : Equivalent Q Q') : sigNeg Q = sigNe
g Q'
参数：h : Equivalent Q Q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `QuadraticMap.Equivalent.sigPos_eq`：QuadraticMap.Equivalent.sigPos_eq (h 
: Equivalent Q Q') : sigPos Q = sigPos Q'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `QuadraticMap.IsometryEquiv.map_app`：map_app (f : Q₁.IsometryEquiv Q₂) (m
 : M₁) : Q₂ (f m) = Q₁ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma QuadraticMap.Equivalent.sigNeg_eq (h : Equivalent Q Q') : sigNeg Q = sigNeg Q' :=
  sigPos_eq <| match h with | ⟨e⟩ => ⟨e, by simp⟩

end LinearOrder

section Field
namespace QuadraticForm

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [Module 𝕜 M] [Module 𝕜 M'] {Q : QuadraticForm 𝕜 M}

/-- Key lemma for Sylvester's law of inertia: the sum of `sigPos Q` and the dimension of any
negative-semidefinite subspace is bounded above by the dimension of the whole space. -/
/-
**QuadraticForm.sigPos_add_finrank_le_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Quadr
aticForm`。
形式化陈述：sigPos_add_finrank_le_of_nonpos [FiniteDimensional 𝕜 M] {V : Subspace 𝕜 M}
 (hV : forall x in V, Q x <= 0) : sigPos Q + Module.finrank 𝕜 V <= Module.finran
k 𝕜 M
参数：hV : forall x in V, Q x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finrank_eq_sigPos_and_posDef`：exists_finrank_eq_sigPos_and_posDef
 [Module.Finite R M] [StrongRankCondition R] : exists V : Submodule R M, Module.
finrank R V = sigPos Q ∧ …
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_add_finrank_le_of_disjoint`：finrank_add_finrank_le_of_
disjoint [FiniteDimensional K V] {s t : Submodule K V} (hdisjoint : Disjoint s t
) : finrank K s + finrank K t <= f…
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p

--- 原说明 ---
Key lemma for Sylvester's law of inertia: the sum of `sigPos Q` and the dimensio
n of any
negative-semidefinite subspace is bounded above by the dimension of the whole sp
ace.
-/
lemma sigPos_add_finrank_le_of_nonpos [FiniteDimensional 𝕜 M]
    {V : Subspace 𝕜 M} (hV : ∀ x ∈ V, Q x ≤ 0) :
    sigPos Q + Module.finrank 𝕜 V ≤ Module.finrank 𝕜 M := by
  obtain ⟨Vp, hr, hVp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  rw [← hr]
  apply Submodule.finrank_add_finrank_le_of_disjoint
  intro W hWp hWm
  rw [le_bot_iff, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx'
  have := hVp ⟨x, hWp hx⟩ (by simpa using hx')
  have := hV x (hWm hx)
  grind [restrict_apply]

variable {ι : Type*} [Fintype ι] {w : ι → 𝕜} [IsStrictOrderedRing 𝕜]
/-
**QuadraticForm.posDef_spanSubset** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma posDef_spanSubset (s : Set ι) (hs : ∀ i ∈ s, 0 < w i) :
    (weightedSumSquares 𝕜 w).restrict (Pi.spanSubset 𝕜 s) |>.PosDef := by
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply, weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i ∈ s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [Pi.mem_spanSubset_iff.mp hv i hi]
  · simp only [ne_eq, Submodule.mk_eq_zero, funext_iff, not_forall, Pi.zero_apply] at hv'
    obtain ⟨i, hi⟩ := hv'
    refine ⟨i, mem_univ _, ?_⟩
    have : i ∈ s := by
      contrapose hi
      exact Pi.mem_spanSubset_iff.mp hv i hi
    exact smul_pos (hs i this) (mul_self_pos.mpr hi)
/-
**QuadraticForm.negSemidef_spanSubset** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma negSemidef_spanSubset (s : Set ι) (hs : ∀ i ∈ s, w i ≤ 0) :
    ∀ x ∈ Pi.spanSubset 𝕜 s, (weightedSumSquares 𝕜 w) x ≤ 0 := by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i ∈ s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [Pi.mem_spanSubset_iff.mp hx i hi, mul_zero, mul_zero]

/-- Key lemma for Sylvester's law of inertia: compute the signature of a weighted sum of squares. -/
/-
**QuadraticForm.sigPos_weightedSumSquares** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticFo
rm`。
形式化陈述：sigPos_weightedSumSquares : sigPos (weightedSumSquares 𝕜 w) = {i | 0 < w i
}.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `sigPos_isGreatest`：sigPos_isGreatest [Module.Finite R M] [StrongRankCond
ition R] : IsGreatest {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q
.restri…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `Pi.dim_spanSubset`：Pi.dim_spanSubset [Finite ι] [Nontrivial R] {s : Set 
ι} : Module.finrank R (Pi.spanSubset R s) = s.ncard
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Signature.0.QuadraticForm.p
osDef_spanSubset`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] {ι 
: Type u_5} [inst_2 : Fintype ι] {w : ι → 𝕜}   [IsStrictOrderedRing 𝕜] (s : Se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用引理 `QuadraticForm.sigPos_add_finrank_le_of_nonpos`：sigPos_add_finrank_le_of_
nonpos [FiniteDimensional 𝕜 M] {V : Subspace 𝕜 M} (hV : forall x in V, Q x <= 0)
 : sigPos Q + Module.finrank 𝕜 V <=…
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Signature.0.QuadraticForm.n
egSemidef_spanSubset`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜]
 {ι : Type u_5} [inst_2 : Fintype ι] {w : ι → 𝕜}   [IsStrictOrderedRing 𝕜] (s : 
Se…

--- 原说明 ---
Key lemma for Sylvester's law of inertia: compute the signature of a weighted su
m of squares.
-/
lemma sigPos_weightedSumSquares :
    sigPos (weightedSumSquares 𝕜 w) = {i | 0 < w i}.ncard := by
  let p : Set ι := {i | 0 < w i}
  let m : Set ι := {i | w i ≤ 0}
  convert_to sigPos _ = p.ncard
  have : p.ncard + m.ncard = Nat.card ι := by
    convert! Set.ncard_add_ncard_compl p
    ext
    grind
  have : p.ncard ≤ sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨Pi.spanSubset 𝕜 p, Pi.dim_spanSubset,
      posDef_spanSubset p (by grind)⟩
  suffices sigPos (weightedSumSquares 𝕜 w) + m.ncard ≤ Nat.card ι by lia
  simpa using sigPos_add_finrank_le_of_nonpos <| negSemidef_spanSubset m (fun _ hi ↦ hi)
/-
**QuadraticForm.sigNeg_weightedSumSquares** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticFo
rm`。
形式化陈述：sigNeg_weightedSumSquares : sigNeg (weightedSumSquares 𝕜 w) = {i | w i < 0
}.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `QuadraticMap.weightedSumSquares_apply`：weightedSumSquares_apply [Monoid 
S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S) (v : ι -> R) : weig
htedSumSquares R w v = ∑ i …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `QuadraticForm.sigPos_weightedSumSquares`：sigPos_weightedSumSquares : sig
Pos (weightedSumSquares 𝕜 w) = {i | 0 < w i}.ncard
-/
lemma sigNeg_weightedSumSquares :
    sigNeg (weightedSumSquares 𝕜 w) = {i | w i < 0}.ncard := by
  simp only [sigNeg]
  convert! sigPos_weightedSumSquares (w := -w) using 2
  · ext; simp
  · simp
/-
**QuadraticForm.sigPos_add_sigNeg_add_radical** 是 Mathlib 中的一个引理，位于命名空间 `Quadrat
icForm`。
形式化陈述：sigPos_add_sigNeg_add_radical [FiniteDimensional 𝕜 M] : sigPos Q + sigNeg 
Q + Module.finrank 𝕜 Q.radical = Module.finrank 𝕜 M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares`：equivalent_weightedSumSquar
es (Q : QuadraticForm K V) : exists w : Fin (Module.finrank K V) -> K, Equivalen
t Q (weightedSumSquares K w)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.Equivalent.sigPos_eq`：QuadraticMap.Equivalent.sigPos_eq (h 
: Equivalent Q Q') : sigPos Q = sigPos Q'
· 使用引理 `QuadraticMap.Equivalent.sigNeg_eq`：QuadraticMap.Equivalent.sigNeg_eq (h 
: Equivalent Q Q') : sigNeg Q = sigNeg Q'
· 使用定理 `QuadraticMap.Equivalent.rank_radical_eq`：∀ {R : Type u_1} {M : Type u_2}
 {M' : Type u_3} {P : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup M
']   [inst_2 : AddCommGroup P…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_fin`：card_fin (n : Nat) : Nat.card (Fin n) = n
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Signature.0.QuadraticForm.s
igPos_add_sigNeg_add_radical₁`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst_1 : Linea
rOrder 𝕜] {ι : Type u_5} [inst_2 : Fintype ι] {w : ι → 𝕜}   [IsStrictOrderedRing
 𝕜],   sigP…
-/
private lemma sigPos_add_sigNeg_add_radical₁ :
    sigPos (weightedSumSquares 𝕜 w) + sigNeg (weightedSumSquares 𝕜 w) +
      Module.finrank 𝕜 (weightedSumSquares 𝕜 w).radical = Nat.card ι := by
  rw [radical_weightedSumSquares, sigPos_weightedSumSquares, sigNeg_weightedSumSquares,
    Pi.dim_spanSubset]
  calc {i | 0 < w i}.ncard + {i | w i < 0}.ncard + {i | w i = 0}.ncard
  _ = {i | 0 < w i}.ncard + {i | w i ≤ 0}.ncard := by
    rw [add_assoc, add_left_cancel_iff, ← Set.ncard_union_eq]
    · congr! 1
      ext
      grind
    · grind [disjoint_iff_ne]
  _ = Set.univ.ncard := by
    rw [← Set.ncard_union_eq]
    · congr! 1
      ext
      grind [le_iff_lt_or_eq]
    · grind [disjoint_iff_ne]
  _ = Nat.card ι := Set.ncard_univ _
/-
**QuadraticForm.sigPos_add_sigNeg_add_radical** 是 Mathlib 中的一个引理，位于命名空间 `Quadrat
icForm`。
形式化陈述：sigPos_add_sigNeg_add_radical [FiniteDimensional 𝕜 M] : sigPos Q + sigNeg 
Q + Module.finrank 𝕜 Q.radical = Module.finrank 𝕜 M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares`：equivalent_weightedSumSquar
es (Q : QuadraticForm K V) : exists w : Fin (Module.finrank K V) -> K, Equivalen
t Q (weightedSumSquares K w)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.Equivalent.sigPos_eq`：QuadraticMap.Equivalent.sigPos_eq (h 
: Equivalent Q Q') : sigPos Q = sigPos Q'
· 使用引理 `QuadraticMap.Equivalent.sigNeg_eq`：QuadraticMap.Equivalent.sigNeg_eq (h 
: Equivalent Q Q') : sigNeg Q = sigNeg Q'
· 使用定理 `QuadraticMap.Equivalent.rank_radical_eq`：∀ {R : Type u_1} {M : Type u_2}
 {M' : Type u_3} {P : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup M
']   [inst_2 : AddCommGroup P…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_fin`：card_fin (n : Nat) : Nat.card (Fin n) = n
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Signature.0.QuadraticForm.s
igPos_add_sigNeg_add_radical₁`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst_1 : Linea
rOrder 𝕜] {ι : Type u_5} [inst_2 : Fintype ι] {w : ι → 𝕜}   [IsStrictOrderedRing
 𝕜],   sigP…
-/
lemma sigPos_add_sigNeg_add_radical [FiniteDimensional 𝕜 M] :
    sigPos Q + sigNeg Q + Module.finrank 𝕜 Q.radical = Module.finrank 𝕜 M := by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w, e⟩ := Q.equivalent_weightedSumSquares
  rw [e.sigPos_eq, e.sigNeg_eq, e.rank_radical_eq]
  convert! QuadraticForm.sigPos_add_sigNeg_add_radical₁ (w := w)
  exact Eq.symm (Nat.card_fin (Module.finrank 𝕜 M))

/-- Uniqueness part of **Sylvester's law of inertia** (positive part):
for any weighted sum of squares equivalent to `Q`,
the number of strictly positive weights is equal to `sigPos Q`. -/
/-
**QuadraticForm.sigPos_of_equiv_weightedSumSquares** 是 Mathlib 中的一个引理，位于命名空间 `Qu
adraticForm`。
形式化陈述：sigPos_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 
𝕜 w)) : sigPos Q = {i | 0 < w i}.ncard
参数：hQ : Equivalent Q (weightedSumSquares 𝕜 w)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.Equivalent.sigPos_eq`：QuadraticMap.Equivalent.sigPos_eq (h 
: Equivalent Q Q') : sigPos Q = sigPos Q'
· 使用引理 `QuadraticForm.sigPos_weightedSumSquares`：sigPos_weightedSumSquares : sig
Pos (weightedSumSquares 𝕜 w) = {i | 0 < w i}.ncard

--- 原说明 ---
Uniqueness part of **Sylvester's law of inertia** (positive part):
for any weighted sum of squares equivalent to `Q`,
the number of strictly positive weights is equal to `sigPos Q`.
-/
lemma sigPos_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigPos Q = {i | 0 < w i}.ncard := by
  rw [hQ.sigPos_eq]
  exact sigPos_weightedSumSquares

/-- Uniqueness part of **Sylvester's law of inertia** (negative part):
for any weighted sum of squares equivalent to `Q`,
the number of strictly negative weights is equal to `sigNeg Q`. -/
/-
**QuadraticForm.sigNeg_of_equiv_weightedSumSquares** 是 Mathlib 中的一个引理，位于命名空间 `Qu
adraticForm`。
形式化陈述：sigNeg_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 
𝕜 w)) : sigNeg Q = {i | w i < 0}.ncard
参数：hQ : Equivalent Q (weightedSumSquares 𝕜 w)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.Equivalent.sigNeg_eq`：QuadraticMap.Equivalent.sigNeg_eq (h 
: Equivalent Q Q') : sigNeg Q = sigNeg Q'
· 使用引理 `QuadraticForm.sigNeg_weightedSumSquares`：sigNeg_weightedSumSquares : sig
Neg (weightedSumSquares 𝕜 w) = {i | w i < 0}.ncard

--- 原说明 ---
Uniqueness part of **Sylvester's law of inertia** (negative part):
for any weighted sum of squares equivalent to `Q`,
the number of strictly negative weights is equal to `sigNeg Q`.
-/
lemma sigNeg_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigNeg Q = {i | w i < 0}.ncard := by
  rw [hQ.sigNeg_eq]
  exact sigNeg_weightedSumSquares

end QuadraticForm

