/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.RingTheory.Algebraic.MvPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic Independence

This file relates algebraic independence and transcendence (or algebraicity) of elements.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence

-/

public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v

variable {ι ι' R : Type*} {S : Type u} {A : Type v} {x : ι → A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- A one-element family `x` is algebraically independent if and only if
its element is transcendental. -/
@[simp]
/-
**algebraicIndependent_unique_type_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_unique_type_iff [Unique ι] : AlgebraicIndependent R x
 ↔ Transcendental R (x default)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff_injective`：transcendental_iff_injective {x : A} : Tra
nscendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
· 使用定理 `algebraicIndependent_iff_injective_aeval`：algebraicIndependent_iff_injec
tive_aeval : AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPoly
nomial ι R ->ₐ[R] A)
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.uniqueAlgEquiv_apply`：∀ (R : Type u) [inst : CommSemiring R
] (σ : Type u_2) [inst_1 : Unique σ] (p : MvPolynomial σ R),   (MvPolynomial.uni
queAlgEquiv R σ) p = Mv…
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A one-element family `x` is algebraically independent if and only if
its element is transcendental.
-/
theorem algebraicIndependent_unique_type_iff [Unique ι] :
    AlgebraicIndependent R x ↔ Transcendental R (x default) := by
  rw [transcendental_iff_injective, algebraicIndependent_iff_injective_aeval]
  let i := uniqueAlgEquiv R ι
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]
/-
**algebraicIndependent_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_singleton_iff [Subsingleton ι] (i : ι) : AlgebraicInd
ependent R x ↔ Transcendental R (x i)
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_unique_type_iff`：algebraicIndependent_unique_type_i
ff [Unique ι] : AlgebraicIndependent R x ↔ Transcendental R (x default)
-/
theorem algebraicIndependent_singleton_iff [Subsingleton ι] (i : ι) :
    AlgebraicIndependent R x ↔ Transcendental R (x i) :=
  letI := uniqueOfSubsingleton i
  algebraicIndependent_unique_type_iff

/-- The one-element family `![x]` is algebraically independent if and only if
`x` is transcendental. -/
/-
**algebraicIndependent_iff_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_iff_transcendental {x : A} : AlgebraicIndependent R !
[x] ↔ Transcendental R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The one-element family `![x]` is algebraically independent if and only if
`x` is transcendental.
-/
theorem algebraicIndependent_iff_transcendental {x : A} :
    AlgebraicIndependent R ![x] ↔ Transcendental R x := by
  simp

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

/-- If a family `x` is algebraically independent, then any of its element is transcendental. -/
/-
**AlgebraicIndependent.transcendental** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndepe
ndent`。
形式化陈述：transcendental (i : ι) : Transcendental R (x i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FinVec.map_eq`：map_eq (f : α -> β) {m} (v : Fin m -> α) : map f v = f ∘ 
v
· 使用定理 `algebraicIndependent_iff_transcendental`：algebraicIndependent_iff_transc
endental {x : A} : AlgebraicIndependent R ![x] ↔ Transcendental R x

--- 原说明 ---
If a family `x` is algebraically independent, then any of its element is transce
ndental.
-/
theorem transcendental (i : ι) : Transcendental R (x i) := by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

/-- If `A/R` is algebraic, then all algebraically independent families are empty. -/
/-
**AlgebraicIndependent.isEmpty_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icIndependent`。
形式化陈述：isEmpty_of_isAlgebraic [Algebra.IsAlgebraic R A] : IsEmpty ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `AlgebraicIndependent.transcendental`：transcendental (i : ι) : Transcende
ntal R (x i)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…

--- 原说明 ---
If `A/R` is algebraic, then all algebraically independent families are empty.
-/
theorem isEmpty_of_isAlgebraic [Algebra.IsAlgebraic R A] : IsEmpty ι := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

end AlgebraicIndependent

/-
**trdeg_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_eq_zero [Algebra.IsAlgebraic R A] : trdeg R A = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `AlgebraicIndependent.isEmpty_of_isAlgebraic`：isEmpty_of_isAlgebraic [Alg
ebra.IsAlgebraic R A] : IsEmpty ι
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
-/
theorem trdeg_eq_zero [Algebra.IsAlgebraic R A] : trdeg R A = 0 :=
  bot_unique <| ciSup_le' fun s ↦ have := s.2.isEmpty_of_isAlgebraic; (Cardinal.mk_eq_zero _).le

variable (R A) in
/-
**trdeg_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_pos [Algebra.Transcendental R A] : 0 < trdeg R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Transcendental.transcendental`：∀ {R : Type u} {A : Type v} {inst
 : CommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.Transc
endental R A], ∃ x, Transce…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_unique_type_iff`：algebraicIndependent_unique_type_i
ff [Unique ι] : AlgebraicIndependent R x ↔ Transcendental R (x default)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem trdeg_pos [Algebra.Transcendental R A] : 0 < trdeg R A :=
  have ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := R) (A := A)
  zero_lt_one.trans_le <| le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨{x}, algebraicIndependent_unique_type_iff.mpr hx⟩ (by simp)
/-
**trdeg_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebraic R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `trdeg_eq_zero`：trdeg_eq_zero [Algebra.IsAlgebraic R A] : trdeg R A = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `trdeg_pos`：trdeg_pos [Algebra.Transcendental R A] : 0 < trdeg R A
-/
theorem trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebraic R A := by
  by_cases h : Algebra.IsAlgebraic R A
  · exact iff_of_true trdeg_eq_zero h
  rw [← not_iff_not]
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at h ⊢
  exact iff_of_true (trdeg_pos R A).ne' h
/-
**trdeg_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_ne_zero_iff : trdeg R A != 0 ↔ Algebra.Transcendental R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `trdeg_eq_zero_iff`：trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebra
ic R A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trdeg_ne_zero_iff : trdeg R A ≠ 0 ↔ Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic, Ne, trdeg_eq_zero_iff]

open AlgebraicIndependent
/-
**AlgebraicIndependent.option_iff_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.option_iff_transcendental (hx : AlgebraicIndependent 
R x) (a : A) : AlgebraicIndependent R (fun o : Option ι => o.elim a x) ↔ Transce
ndental (adjoin R (range x)) a
参数：hx : AlgebraicIndependent R x；a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff_injective_aeval`：algebraicIndependent_iff_injec
tive_aeval : AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPoly
nomial ι R ->ₐ[R] A)
· 使用定理 `transcendental_iff_injective`：transcendental_iff_injective {x : A} : Tra
nscendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin`
：AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin (hx : A
lgebraicIndependent R x) (a : A) : RingHom.comp (↑(Polynomial…
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem AlgebraicIndependent.option_iff_transcendental (hx : AlgebraicIndependent R x) (a : A) :
    AlgebraicIndependent R (fun o : Option ι ↦ o.elim a x) ↔
      Transcendental (adjoin R (range x)) a := by
  rw [algebraicIndependent_iff_injective_aeval, transcendental_iff_injective,
    ← AlgHom.coe_toRingHom, ← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin,
    RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx).bijective
/-
**AlgebraicIndependent.option_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.option_iff {a : A} : AlgebraicIndependent R (fun o : 
Option ι => o.elim a x) ↔ AlgebraicIndependent R x ∧ Transcendental (adjoin R (r
ange x)) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicIndependent.option_iff_transcendental`：AlgebraicIndependent.opt
ion_iff_transcendental (hx : AlgebraicIndependent R x) (a : A) : AlgebraicIndepe
ndent R (fun o : Option ι => o.elim …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AlgebraicIndependent.option_iff {a : A} :
    AlgebraicIndependent R (fun o : Option ι ↦ o.elim a x) ↔
      AlgebraicIndependent R x ∧ Transcendental (adjoin R (range x)) a :=
  ⟨fun h ↦ have := h.comp _ (Option.some_injective _); ⟨this,
    (this.option_iff_transcendental _).mp h⟩, fun h ↦ (h.1.option_iff_transcendental _).mpr h.2⟩
/-
**AlgebraicIndepOn.insert_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndepOn.insert_iff {s : Set ι} {i : ι} (h : i ∉ s) : AlgebraicInd
epOn R x (insert i s) ↔ AlgebraicIndepOn R x s ∧ Transcendental (adjoin R (x '' 
s)) (x i)
参数：h : i ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraicIndependent_equiv`：algebraicIndependent_equiv (e : ι ≃ ι') {f :
 ι' -> A} : AlgebraicIndependent R (f ∘ e) ↔ AlgebraicIndependent R f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicIndependent.option_iff`：AlgebraicIndependent.option_iff {a : A}
 : AlgebraicIndependent R (fun o : Option ι => o.elim a x) ↔ AlgebraicIndependen
t R x ∧ Transcendenta…
-/
theorem AlgebraicIndepOn.insert_iff {s : Set ι} {i : ι} (h : i ∉ s) :
    AlgebraicIndepOn R x (insert i s) ↔
      AlgebraicIndepOn R x s ∧ Transcendental (adjoin R (x '' s)) (x i) := by
  classical simp_rw [← algebraicIndependent_equiv (subtypeInsertEquivOption h).symm,
    AlgebraicIndepOn]
  convert! option_iff (x := fun i : s ↦ x i) (a := x i) using 2
  · ext (_ | _) <;> rfl
  · rw [Set.image_eq_range]
/-
**AlgebraicIndepOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndepOn`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : Type v} {x : ι → A} [inst : CommRing 
R] [inst_1 : CommRing A]   [inst_2 : Algebra R A] {s : Set ι} {i : ι},   Algebra
icIndepOn R x s → Transcendental (↥(Algebra.adjoin R (x '' s))) (x i) → Algebrai
cIndepOn R x (insert i s)
参数：↥(Algebra.adjoin R (x '' s))；x i；insert i s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicIndepOn.insert_iff`：AlgebraicIndepOn.insert_iff {s : Set ι} {i 
: ι} (h : i ∉ s) : AlgebraicIndepOn R x (insert i s) ↔ AlgebraicIndepOn R x s ∧ 
Transcendental (a…
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
protected theorem AlgebraicIndepOn.insert {s : Set ι} {i : ι} (hs : AlgebraicIndepOn R x s)
    (hi : Transcendental (adjoin R (x '' s)) (x i)) : AlgebraicIndepOn R x (insert i s) := by
  nontriviality R
  have := hs.algebraMap_injective.nontrivial
  exact (insert_iff fun h ↦ hi <| isAlgebraic_algebraMap
    (⟨_, subset_adjoin ⟨i, h, rfl⟩⟩ : adjoin R (x '' s))).mpr ⟨hs, hi⟩

set_option backward.isDefEq.respectTransparency false in
/-
**algebraicIndependent_of_set_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_of_set_of_finite (s : Set ι) (ind : AlgebraicIndepend
ent R fun i : s => x i) (H : forall t : Set ι, t.Finite -> AlgebraicIndependent 
R (fun i : t => x i) -> forall i ∉ s, i ∉ t -> Transcendental (adjoin R (x '' t)
) (x i)) : AlgebraicIndependent R x
参数：s : Set ι；ind : AlgebraicIndependent R fun i : s => x i；H : forall t : Set ι,
 t.Finite -> AlgebraicIndependent R (fun i : t => x i) -> forall i ∉ s, i ∉ t ->
 Transcendental (adjoin R (x '' t)) (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_of_finite_type`：algebraicIndependent_of_finite_type
 (H : forall t : Set ι, t.Finite -> AlgebraicIndependent R fun i : t => x i) : A
lgebraicIndependent R x
· 使用定理 `Set.Finite.induction_on_subset`：∀ {α : Type u} {motive : (s : Set α) → s
.Finite → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ →     (∀ {a : α} {t : 
Set α}, a ∈ s → ∀ (h…
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.setCongr_apply`：∀ {α : Type u_3} {s t : Set α} (h : s = t) (a : { 
a // (fun x => x ∈ s) a }), (Equiv.setCongr h) a = ⟨↑a, ⋯⟩
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicIndependent.option_iff_transcendental`：AlgebraicIndependent.opt
ion_iff_transcendental (hx : AlgebraicIndependent R x) (a : A) : AlgebraicIndepe
ndent R (fun o : Option ι => o.elim …
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
（共 35 条，此处仅展示前 30 条）
-/
theorem algebraicIndependent_of_set_of_finite (s : Set ι)
    (ind : AlgebraicIndependent R fun i : s ↦ x i)
    (H : ∀ t : Set ι, t.Finite → AlgebraicIndependent R (fun i : t ↦ x i) →
      ∀ i ∉ s, i ∉ t → Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x := by
  classical
  refine algebraicIndependent_of_finite_type fun t hfin ↦ ?_
  suffices AlgebraicIndependent R fun i : ↥(t ∩ s ∪ t \ s) ↦ x i from
    this.comp (Equiv.setCongr (t.inter_union_sdiff s).symm) (Equiv.injective _)
  refine hfin.sdiff.induction_on_subset _ (ind.comp (inclusion <| by simp) (inclusion_injective _))
    fun {a u} ha hu ha' h ↦ ?_
  have : a ∉ t ∩ s ∪ u := (·.elim (ha.2 ·.2) ha')
  convert!
    (((image_eq_range .. ▸ h.option_iff_transcendental <| x a).2 <|
              H _ (hfin.subset (union_subset inter_subset_left <| hu.trans sdiff_subset)) h a ha.2
                this).comp
          _ (subtypeInsertEquivOption this).injective).comp
      (Equiv.setCongr union_insert) (Equiv.injective _) with
    x
  by_cases h : ↑x = a <;> simp [h, Set.subtypeInsertEquivOption]

/-- Variant of `algebraicIndependent_of_finite_type` using `Transcendental`. -/
/-
**algebraicIndependent_of_finite_type'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_of_finite_type' (hinj : Injective (algebraMap R A)) (
H : forall t : Set ι, t.Finite -> AlgebraicIndependent R (fun i : t => x i) -> f
orall i ∉ t, Transcendental (adjoin R (x '' t)) (x i)) : AlgebraicIndependent R 
x
参数：hinj : Injective (algebraMap R A)；H : forall t : Set ι, t.Finite -> Algebraic
Independent R (fun i : t => x i) -> forall i ∉ t, Transcendental (adjoin R (x ''
 t)) (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_of_set_of_finite`：algebraicIndependent_of_set_of_fi
nite (s : Set ι) (ind : AlgebraicIndependent R fun i : s => x i) (H : forall t :
 Set ι, t.Finite -> Algebra…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_empty_type_iff`：algebraicIndependent_empty_type_iff
 [IsEmpty ι] : AlgebraicIndependent R x ↔ Injective (algebraMap R A)
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅

--- 原说明 ---
Variant of `algebraicIndependent_of_finite_type` using `Transcendental`.
-/
theorem algebraicIndependent_of_finite_type'
    (hinj : Injective (algebraMap R A))
    (H : ∀ t : Set ι, t.Finite → AlgebraicIndependent R (fun i : t ↦ x i) →
      ∀ i ∉ t, Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x :=
  algebraicIndependent_of_set_of_finite ∅ (algebraicIndependent_empty_type_iff.mpr hinj)
    fun t ht ind i _ ↦ H t ht ind i

/-- Variant of `algebraicIndependent_of_finite` using `Transcendental`. -/
/-
**algebraicIndependent_of_finite'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_of_finite' (s : Set A) (hinj : Injective (algebraMap 
R A)) (H : forall t subseteq s, t.Finite -> AlgebraicIndependent R ((↑) : t -> A
) -> forall a in s, a ∉ t -> Transcendental (adjoin R t) a) : AlgebraicIndepende
nt R ((↑) : s -> A)
参数：s : Set A；hinj : Injective (algebraMap R A)；H : forall t subseteq s, t.Finite
 -> AlgebraicIndependent R ((↑) : t -> A) -> forall a in s, a ∉ t -> Transcenden
tal (adjoin R t) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_of_finite_type'`：algebraicIndependent_of_finite_typ
e' (hinj : Injective (algebraMap R A)) (H : forall t : Set ι, t.Finite -> Algebr
aicIndependent R (fun i : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `AlgebraicIndependent.image`：AlgebraicIndependent.image {ι} {s : Set ι} {
f : ι -> A} (hs : AlgebraicIndependent R fun x : s => f x) : AlgebraicIndependen
t R fun x : f ''…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
Variant of `algebraicIndependent_of_finite` using `Transcendental`.
-/
theorem algebraicIndependent_of_finite' (s : Set A)
    (hinj : Injective (algebraMap R A))
    (H : ∀ t ⊆ s, t.Finite → AlgebraicIndependent R ((↑) : t → A) →
      ∀ a ∈ s, a ∉ t → Transcendental (adjoin R t) a) :
    AlgebraicIndependent R ((↑) : s → A) :=
  algebraicIndependent_of_finite_type' hinj fun t hfin h i hi ↦ H _
    (by rintro _ ⟨x, _, rfl⟩; exact x.2) (hfin.image _) h.image _ i.2
    (mt Subtype.val_injective.mem_set_image.mp hi)

namespace AlgebraicIndependent

/-
**AlgebraicIndependent.sumElim_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndepende
nt`。
形式化陈述：sumElim_iff {ι'} {y : ι' -> A} : AlgebraicIndependent R (Sum.elim y x) ↔ A
lgebraicIndependent R x ∧ AlgebraicIndependent (adjoin R (range x)) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用引理 `MvPolynomial.sumAlgEquiv_X_inl`：sumAlgEquiv_X_inl (c : S₁) : sumAlgEquiv
 R S₁ S₂ (X <| .inl c) = X c
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MvPolynomial.sumAlgEquiv_X_inr`：sumAlgEquiv_X_inr (c : S₂) : sumAlgEquiv
 R S₁ S₂ (X <| .inr c) = C (X c)
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `AlgebraicIndependent.aevalEquiv_apply_coe`：∀ {ι : Type u_1} {R : Type u_
3} {A : Type u_5} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A]   [inst_
2 : Algebra R A] (hx : Algebrai…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sumElim_iff {ι'} {y : ι' → A} : AlgebraicIndependent R (Sum.elim y x) ↔
    AlgebraicIndependent R x ∧ AlgebraicIndependent (adjoin R (range x)) y := by
  by_cases hx : AlgebraicIndependent R x; swap
  · exact ⟨fun h ↦ (hx <| by apply h.comp _ Sum.inr_injective).elim, fun h ↦ (hx h.1).elim⟩
  let e := (sumAlgEquiv R ι' ι).trans (mapAlgEquiv _ hx.aevalEquiv)
  have : aeval (Sum.elim y x) = ((aeval y).restrictScalars R).comp e.toAlgHom := by
    ext (_ | _) <;> simp [e]
  simp_rw [hx, AlgebraicIndependent, this]; simp
/-
**AlgebraicIndependent.iff_adjoin_image** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInde
pendent`。
形式化陈述：iff_adjoin_image (s : Set ι) : AlgebraicIndependent R x ↔ AlgebraicIndepen
dent R (fun i : s => x i) ∧ AlgebraicIndepOn (adjoin R (x '' s)) x sᶜ
参数：s : Set ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraicIndependent_equiv'`：algebraicIndependent_equiv' (e : ι ≃ ι') {f
 : ι' -> A} {g : ι -> A} (h : f ∘ e = g) : AlgebraicIndependent R g ↔ AlgebraicI
ndependent R f
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `AlgebraicIndependent.sumElim_iff`：sumElim_iff {ι'} {y : ι' -> A} : Algeb
raicIndependent R (Sum.elim y x) ↔ AlgebraicIndependent R x ∧ AlgebraicIndepende
nt (adjoin R (range x)…
-/
theorem iff_adjoin_image (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : s ↦ x i) ∧
      AlgebraicIndepOn (adjoin R (x '' s)) x sᶜ := by
  rw [show x '' s = range fun i : s ↦ x i by ext; simp]
  convert! ← sumElim_iff
  classical apply algebraicIndependent_equiv' ((Equiv.sumComm ..).trans (Equiv.Set.sumCompl ..))
  ext (_ | _) <;> rfl
/-
**AlgebraicIndependent.iff_adjoin_image_compl** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icIndependent`。
形式化陈述：iff_adjoin_image_compl (s : Set ι) : AlgebraicIndependent R x ↔ AlgebraicI
ndependent R (fun i : ↥sᶜ => x i) ∧ AlgebraicIndepOn (adjoin R (x '' sᶜ)) x s
参数：s : Set ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `AlgebraicIndependent.iff_adjoin_image`：iff_adjoin_image (s : Set ι) : Al
gebraicIndependent R x ↔ AlgebraicIndependent R (fun i : s => x i) ∧ AlgebraicIn
depOn (adjoin R (x '' s)) x…
-/
theorem iff_adjoin_image_compl (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : ↥sᶜ ↦ x i) ∧
      AlgebraicIndepOn (adjoin R (x '' sᶜ)) x s := by
  convert! ← iff_adjoin_image _; apply compl_compl
/-
**AlgebraicIndependent.iff_transcendental_adjoin_image** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicIndependent`。
形式化陈述：iff_transcendental_adjoin_image (i : ι) : AlgebraicIndependent R x ↔ Algeb
raicIndependent R (fun j : {j // j != i} => x j) ∧ Transcendental (adjoin R (x '
' {i}ᶜ)) (x i)
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AlgebraicIndependent.iff_adjoin_image_compl`：iff_adjoin_image_compl (s :
 Set ι) : AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : ↥sᶜ => x i)
 ∧ AlgebraicIndepOn (adjoin R (x …
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `algebraicIndependent_unique_type_iff`：algebraicIndependent_unique_type_i
ff [Unique ι] : AlgebraicIndependent R x ↔ Transcendental R (x default)
-/
theorem iff_transcendental_adjoin_image (i : ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun j : {j // j ≠ i} ↦ x j) ∧
      Transcendental (adjoin R (x '' {i}ᶜ)) (x i) :=
  (iff_adjoin_image_compl _).trans <| and_congr_right
    fun _ ↦ algebraicIndependent_unique_type_iff (ι := {j // j = i})

variable (hx : AlgebraicIndependent R x)
include hx
/-
**AlgebraicIndependent.sumElim** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：sumElim {ι'} {y : ι' -> A} (hy : AlgebraicIndependent (adjoin R (range x))
 y) : AlgebraicIndependent R (Sum.elim y x)
参数：hy : AlgebraicIndependent (adjoin R (range x)) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicIndependent.sumElim_iff`：sumElim_iff {ι'} {y : ι' -> A} : Algeb
raicIndependent R (Sum.elim y x) ↔ AlgebraicIndependent R x ∧ AlgebraicIndepende
nt (adjoin R (range x)…
-/
theorem sumElim {ι'} {y : ι' → A} (hy : AlgebraicIndependent (adjoin R (range x)) y) :
    AlgebraicIndependent R (Sum.elim y x) :=
  sumElim_iff.mpr ⟨hx, hy⟩
/-
**AlgebraicIndependent.sumElim_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInde
pendent`。
形式化陈述：sumElim_of_tower {ι'} {y : ι' -> A} (hxS : range x subseteq range (algebra
Map S A)) (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y x
)
参数：hxS : range x subseteq range (algebraMap S A)；hy : AlgebraicIndependent S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicIndependent.sumElim`：sumElim {ι'} {y : ι' -> A} (hy : Algebraic
Independent (adjoin R (range x)) y) : AlgebraicIndependent R (Sum.elim y x)
· 使用定理 `AlgebraicIndependent.restrictScalars`：AlgebraicIndependent.restrictScala
rs {K : Type*} [CommRing K] [Algebra R K] [Algebra K A] [IsScalarTower R K A] (h
inj : Function.Injective (…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
-/
theorem sumElim_of_tower {ι'} {y : ι' → A} (hxS : range x ⊆ range (algebraMap S A))
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y x) := by
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R S A) hy.algebraMap_injective
  set Rx := adjoin R (range x)
  let _ : Algebra Rx S :=
    (e.symm.toAlgHom.comp <| Subalgebra.inclusion <| adjoin_le hxS).toAlgebra
  have : IsScalarTower Rx S A := .of_algebraMap_eq fun x ↦ show _ = (e (e.symm _)).1 by simp
  refine hx.sumElim (hy.restrictScalars (e.symm.injective.comp ?_))
  simpa only [AlgHom.coe_toRingHom] using Subalgebra.inclusion_injective _

omit hx in
/-
**AlgebraicIndependent.sumElim_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndepend
ent`。
形式化陈述：sumElim_comp {ι'} {x : ι -> S} {y : ι' -> A} (hx : AlgebraicIndependent R 
x) (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y (algebra
Map S A ∘ x))
参数：hx : AlgebraicIndependent R x；hy : AlgebraicIndependent S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.sumElim_of_tower`：sumElim_of_tower {ι'} {y : ι' -> 
A} (hxS : range x subseteq range (algebraMap S A)) (hy : AlgebraicIndependent S 
y) : AlgebraicIndependent R…
· 使用定理 `AlgebraicIndependent.map'`：map' {f : A ->ₐ[R] A'} (hf_inj : Injective f)
 : AlgebraicIndependent R (f ∘ x)
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem sumElim_comp {ι'} {x : ι → S} {y : ι' → A} (hx : AlgebraicIndependent R x)
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y (algebraMap S A ∘ x)) :=
  (hx.map' (f := IsScalarTower.toAlgHom R S A) hy.algebraMap_injective).sumElim_of_tower
    (range_comp_subset_range ..) hy
/-
**AlgebraicIndependent.adjoin_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIn
dependent`。
形式化陈述：adjoin_of_disjoint {s t : Set ι} (h : Disjoint s t) : AlgebraicIndependent
 (adjoin R (x '' s)) fun i : t => x i
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicIndependent.iff_adjoin_image`：iff_adjoin_image (s : Set ι) : Al
gebraicIndependent R x ↔ AlgebraicIndependent R (fun i : s => x i) ∧ AlgebraicIn
depOn (adjoin R (x '' s)) x…
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem adjoin_of_disjoint {s t : Set ι} (h : Disjoint s t) :
    AlgebraicIndependent (adjoin R (x '' s)) fun i : t ↦ x i :=
  ((iff_adjoin_image s).mp hx).2.comp (inclusion _) (inclusion_injective h.subset_compl_left)
/-
**AlgebraicIndependent.adjoin_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicI
ndependent`。
形式化陈述：adjoin_iff_disjoint [Nontrivial A] {s t : Set ι} : (AlgebraicIndependent (
adjoin R (x '' s)) fun i : t => x i) ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `AlgebraicIndependent.transcendental`：transcendental (i : ι) : Transcende
ntal R (x i)
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `AlgebraicIndependent.adjoin_of_disjoint`：adjoin_of_disjoint {s t : Set ι
} (h : Disjoint s t) : AlgebraicIndependent (adjoin R (x '' s)) fun i : t => x i
-/
theorem adjoin_iff_disjoint [Nontrivial A] {s t : Set ι} :
    (AlgebraicIndependent (adjoin R (x '' s)) fun i : t ↦ x i) ↔ Disjoint s t := by
  refine ⟨fun ind ↦ of_not_not fun ndisj ↦ ?_, adjoin_of_disjoint hx⟩
  have ⟨i, hs, ht⟩ := Set.not_disjoint_iff.mp ndisj
  refine ind.transcendental ⟨i, ht⟩ (isAlgebraic_algebraMap (⟨_, subset_adjoin ?_⟩ : adjoin R _))
  exact ⟨i, hs, rfl⟩
/-
**AlgebraicIndependent.transcendental_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cIndependent`。
形式化陈述：transcendental_adjoin {s : Set ι} {i : ι} (hi : i ∉ s) : Transcendental (a
djoin R (x '' s)) (x i)
参数：hi : i ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_singleton_iff`：algebraicIndependent_singleton_iff [
Subsingleton ι] (i : ι) : AlgebraicIndependent R x ↔ Transcendental R (x i)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicIndependent.adjoin_of_disjoint`：adjoin_of_disjoint {s t : Set ι
} (h : Disjoint s t) : AlgebraicIndependent (adjoin R (x '' s)) fun i : t => x i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
-/
theorem transcendental_adjoin {s : Set ι} {i : ι} (hi : i ∉ s) :
    Transcendental (adjoin R (x '' s)) (x i) := by
  convert! ← hx.adjoin_of_disjoint (Set.disjoint_singleton_right.mpr hi)
  rw [algebraicIndependent_singleton_iff ⟨i, rfl⟩]
/-
**AlgebraicIndependent.transcendental_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicIndependent`。
形式化陈述：transcendental_adjoin_iff [Nontrivial A] {s : Set ι} {i : ι} : Transcenden
tal (adjoin R (x '' s)) (x i) ↔ i ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `algebraicIndependent_singleton_iff`：algebraicIndependent_singleton_iff [
Subsingleton ι] (i : ι) : AlgebraicIndependent R x ↔ Transcendental R (x i)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicIndependent.adjoin_iff_disjoint`：adjoin_iff_disjoint [Nontrivia
l A] {s t : Set ι} : (AlgebraicIndependent (adjoin R (x '' s)) fun i : t => x i)
 ↔ Disjoint s t
-/
theorem transcendental_adjoin_iff [Nontrivial A] {s : Set ι} {i : ι} :
    Transcendental (adjoin R (x '' s)) (x i) ↔ i ∉ s := by
  rw [← Set.disjoint_singleton_right]
  convert! ← hx.adjoin_iff_disjoint (t := { i })
  rw [algebraicIndependent_singleton_iff ⟨i, rfl⟩]

end AlgebraicIndependent

open Cardinal in
/-
**lift_trdeg_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_trdeg_add_le [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A] : l
ift.{v} (trdeg R S) + lift.{u} (trdeg S A) <= lift.{u} (trdeg R A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.ciSup_add_ciSup`：∀ {ι : Type u} {ι' : Type w} (f : ι → Cardinal
.{v}) [Nonempty ι] [Nonempty ι'],   BddAbove (Set.range f) →     ∀ (g : ι' → Car
dinal.{v}), Bd…
· 使用定理 `instNonemptySubtypeSetAlgebraicIndepOnIdOfFaithfulSMul`：∀ {R : Type u_2}
 {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [
FaithfulSMul R A],   Nonempty { s // Algebra…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `AlgebraicIndependent.sumElim_comp`：sumElim_comp {ι'} {x : ι -> S} {y : ι
' -> A} (hx : AlgebraicIndependent R x) (hy : AlgebraicIndependent S y) : Algebr
aicIndependent R (Sum.e…
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `AlgebraicIndependent.to_subtype_range`：AlgebraicIndependent.to_subtype_r
ange (hx : AlgebraicIndependent R x) : AlgebraicIndependent R ((↑) : range x -> 
A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lift_trdeg_add_le [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A] :
    lift.{v} (trdeg R S) + lift.{u} (trdeg S A) ≤ lift.{u} (trdeg R A) := by
  simp_rw [trdeg, lift_iSup bddAbove_of_small]
  simp_rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small,
    add_comm (lift.{v, u} _), ← mk_sum]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le bddAbove_of_small ⟨_, this.to_subtype_range⟩ ?_
  rw [← lift_umax, mk_range_eq_of_injective this.injective, lift_id']
/-
**trdeg_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_add_le [Nontrivial R] {A : Type u} [CommRing A] [Algebra R A] [Algeb
ra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] : trdeg R S 
+ trdeg S A <= trdeg R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_trdeg_add_le`：lift_trdeg_add_le [Nontrivial R] [FaithfulSMul R S] [
FaithfulSMul S A] : lift.{v} (trdeg R S) + lift.{u} (trdeg S A) <= lift.{u} (trd
eg R A)
-/
theorem trdeg_add_le [Nontrivial R] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A ≤ trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_le

/-- If for each `i : ι`, `f_i : R[X]` is transcendental over `R`, then `{f_i(X_i) | i : ι}`
in `MvPolynomial ι R` is algebraically independent over `R`. -/
/-
**MvPolynomial.algebraicIndependent_polynomial_aeval_X** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MvPolynomial.algebraicIndependent_polynomial_aeval_X (f : ι -> Polynomial 
R) (hf : forall i, Transcendental R (f i)) : AlgebraicIndependent R fun i => Pol
ynomial.aeval (X i : MvPolynomial ι R) (f i)
参数：f : ι -> Polynomial R；hf : forall i, Transcendental R (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_of_finite_type'`：algebraicIndependent_of_finite_typ
e' (hinj : Injective (algebraMap R A)) (H : forall t : Set ι, t.Finite -> Algebr
aicIndependent R (fun i : …
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `Transcendental.of_tower_top_of_subalgebra_le`：Transcendental.of_tower_to
p_of_subalgebra_le {A B : Subalgebra R S} (hle : A <= B) {x : S} (h : Transcende
ntal B x) : Transcendental A x
· 使用定理 `MvPolynomial.transcendental_supported_polynomial_aeval_X`：transcendental
_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s) {f : R[X]} (hf : T
ranscendental R f) : Transcendental (supported…

--- 原说明 ---
If for each `i : ι`, `f_i : R[X]` is transcendental over `R`, then `{f_i(X_i) | 
i : ι}`
in `MvPolynomial ι R` is algebraically independent over `R`.
-/
theorem MvPolynomial.algebraicIndependent_polynomial_aeval_X
    (f : ι → Polynomial R) (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i) := by
  set x := fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ _ i hi ↦ ?_
  have hle : adjoin R (x '' t) ≤ supported R t := by
    rw [Algebra.adjoin_le_iff, Set.image_subset_iff]
    intro _ h
    rw [Set.mem_preimage]
    refine Algebra.adjoin_mono ?_ (Polynomial.aeval_mem_adjoin_singleton R _)
    simp_rw [singleton_subset_iff, Set.mem_image_of_mem _ h]
  exact (transcendental_supported_polynomial_aeval_X R hi (hf i)).of_tower_top_of_subalgebra_le hle

/-- If `{x_i : A | i : ι}` is algebraically independent over `R`, and for each `i`,
`f_i : R[X]` is transcendental over `R`, then `{f_i(x_i) | i : ι}` is also
algebraically independent over `R`. -/
/-
**AlgebraicIndependent.polynomial_aeval_of_transcendental** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：AlgebraicIndependent.polynomial_aeval_of_transcendental (hx : AlgebraicInd
ependent R x) {f : ι -> Polynomial R} (hf : forall i, Transcendental R (f i)) : 
AlgebraicIndependent R fun i => Polynomial.aeval (x i) (f i)
参数：hx : AlgebraicIndependent R x；hf : forall i, Transcendental R (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicIndependent.aeval_of_algebraicIndependent`：aeval_of_algebraicIn
dependent {f : ι -> MvPolynomial ι R} (hf : AlgebraicIndependent R f) : Algebrai
cIndependent R fun i => aeval x (f i)
· 使用定理 `MvPolynomial.algebraicIndependent_polynomial_aeval_X`：MvPolynomial.algeb
raicIndependent_polynomial_aeval_X (f : ι -> Polynomial R) (hf : forall i, Trans
cendental R (f i)) : AlgebraicIndependent …

--- 原说明 ---
If `{x_i : A | i : ι}` is algebraically independent over `R`, and for each `i`,
`f_i : R[X]` is transcendental over `R`, then `{f_i(x_i) | i : ι}` is also
algebraically independent over `R`.
-/
theorem AlgebraicIndependent.polynomial_aeval_of_transcendental
    (hx : AlgebraicIndependent R x)
    {f : ι → Polynomial R} (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (x i) (f i) := by
  convert! aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp
