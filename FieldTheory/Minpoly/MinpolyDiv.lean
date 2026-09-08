/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Results about `minpoly R x / (X - C x)`

## Main definition
- `minpolyDiv`: The polynomial `minpoly R x / (X - C x)`.

We used the contents of this file to describe the dual basis of a power basis under the trace form.
See `traceForm_dualBasis_powerBasis_eq`.

## Main results
- `span_coeff_minpolyDiv`: The coefficients of `minpolyDiv` span `R<x>`.
-/

@[expose] public section

open Polynomial Module Algebra

variable (R K) {L S} [CommRing R] [Field K] [Field L] [CommRing S] [Algebra R S] [Algebra K L]
variable (x : S)

/-- `minpolyDiv R x : S[X]` for `x : S` is the polynomial `minpoly R x / (X - C x)`. -/
/-
**minpolyDiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：minpolyDiv : S[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`minpolyDiv R x : S[X]` for `x : S` is the polynomial `minpoly R x / (X - C x)`.
-/
noncomputable def minpolyDiv : S[X] := (minpoly R x).map (algebraMap R S) /ₘ (X - C x)
/-
**minpolyDiv_spec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly R x).map (algebraM
ap R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.mul_divByMonic_eq_iff_isRoot`：mul_divByMonic_eq_iff_isRoot : 
(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
lemma minpolyDiv_spec :
    minpolyDiv R x * (X - C x) = (minpoly R x).map (algebraMap R S) := by
  delta minpolyDiv
  rw [mul_comm, mul_divByMonic_eq_iff_isRoot, IsRoot, eval_map_algebraMap, minpoly.aeval]
/-
**coeff_minpolyDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i = algebraMap R S (coeff (m
inpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i =
    algebraMap R S (coeff (minpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x := by
  rw [← coeff_map, ← minpolyDiv_spec R x]; simp [mul_sub]

variable {R x}
/-
**minpolyDiv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_eq_zero (hx : ¬IsIntegral R x) : minpolyDiv R x = 0
参数：hx : ¬IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.zero_divByMonic`：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
-/
lemma minpolyDiv_eq_zero (hx : ¬IsIntegral R x) : minpolyDiv R x = 0 := by
  delta minpolyDiv minpoly
  rw [dif_neg hx, Polynomial.map_zero, zero_divByMonic]
/-
**eval_minpolyDiv_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eval_minpolyDiv_self : (minpolyDiv R x).eval x = aeval x (derivative <| mi
npoly R x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_minpolyDiv_self : (minpolyDiv R x).eval x = aeval x (derivative <| minpoly R x) := by
  rw [← eval_map_algebraMap, ← derivative_map, ← minpolyDiv_spec R x]; simp
/-
**minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero [IsDomain S] {y} (hxy : y !
= x) (hy : aeval y (minpoly R x) = 0) : (minpolyDiv R x).eval y = 0
参数：hxy : y != x；hy : aeval y (minpoly R x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
lemma minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero [IsDomain S]
    {y} (hxy : y ≠ x) (hy : aeval y (minpoly R x) = 0) : (minpolyDiv R x).eval y = 0 := by
  rw [← eval_map_algebraMap, ← minpolyDiv_spec R x] at hy
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by rwa [sub_eq_zero])
/-
**eval** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_minpolyDiv_of_eval₂_eq_zero {T} [CommRing T]
    [IsDomain T] [DecidableEq T] {x y}
    (σ : S →+* T) (hy : eval₂ (σ.comp (algebraMap R S)) y (minpoly R x) = 0) :
    eval₂ σ y (minpolyDiv R x) =
      if σ x = y then σ (aeval x (derivative <| minpoly R x)) else 0 := by
  split_ifs with h
  · rw [← h, eval₂_hom, eval_minpolyDiv_self]
  · rw [← eval₂_map, ← minpolyDiv_spec] at hy
    simpa [sub_eq_zero, Ne.symm h] using hy
/-
**eval** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_minpolyDiv_self {T} [CommRing T] [Algebra R T] [IsDomain T] [DecidableEq T] (x : S)
    (σ₁ σ₂ : S →ₐ[R] T) :
    eval₂ σ₁ (σ₂ x) (minpolyDiv R x) =
      if σ₁ x = σ₂ x then σ₁ (aeval x (derivative <| minpoly R x)) else 0 := by
  apply eval₂_minpolyDiv_of_eval₂_eq_zero
  rw [AlgHom.comp_algebraMap, ← σ₂.comp_algebraMap, ← eval₂_map, ← RingHom.coe_coe, eval₂_hom,
    eval_map_algebraMap, minpoly.aeval, map_zero]
/-
**eval_minpolyDiv_of_aeval_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eval_minpolyDiv_of_aeval_eq_zero [IsDomain S] [DecidableEq S] {y} (hy : ae
val y (minpoly R x) = 0) : (minpolyDiv R x).eval y = if x = y then aeval x (deri
vative <| minpoly R x) else 0
参数：hy : aeval y (minpoly R x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用引理 `eval₂_minpolyDiv_of_eval₂_eq_zero`：eval₂_minpolyDiv_of_eval₂_eq_zero {T}
 [CommRing T] [IsDomain T] [DecidableEq T] {x y} (σ : S ->+* T) (hy : eval₂ (σ.c
omp (algebraMap R S)) y…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
-/
lemma eval_minpolyDiv_of_aeval_eq_zero [IsDomain S] [DecidableEq S]
    {y} (hy : aeval y (minpoly R x) = 0) :
    (minpolyDiv R x).eval y = if x = y then aeval x (derivative <| minpoly R x) else 0 := by
  rw [eval, eval₂_minpolyDiv_of_eval₂_eq_zero, RingHom.id_apply, RingHom.id_apply]
  simpa [aeval_def] using hy
/-
**coeff_minpolyDiv_mem_adjoin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeff_minpolyDiv_mem_adjoin (x : S) (i) : coeff (minpolyDiv R x) i in R[x]
参数：x : S；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coeff_minpolyDiv`：coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i = alge
braMap R S (coeff (minpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma coeff_minpolyDiv_mem_adjoin (x : S) (i) :
    coeff (minpolyDiv R x) i ∈ R[x] := by
  by_contra H
  have : ∀ j, coeff (minpolyDiv R x) (i + j) ∉ R[x] := by
    intro j; induction j with
    | zero => exact H
    | succ j IH =>
      intro H; apply IH
      rw [coeff_minpolyDiv]
      refine add_mem ?_ (mul_mem H (self_mem_adjoin_singleton R x))
      exact Subalgebra.algebraMap_mem _ _
  apply this (natDegree (minpolyDiv R x) + 1)
  rw [coeff_eq_zero_of_natDegree_lt]
  · exact zero_mem _
  · lia

section IsIntegral
variable (hx : IsIntegral R x)
include hx

/-
**minpolyDiv_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x ≠ 0 := by
  intro e
  have := minpolyDiv_spec R x
  rw [e, zero_mul] at this
  exact ((minpoly.monic hx).map (algebraMap R S)).ne_zero this.symm
/-
**minpolyDiv_monic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_monic : Monic (minpolyDiv R x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用引理 `minpolyDiv_ne_zero`：minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x !
= 0
-/
lemma minpolyDiv_monic : Monic (minpolyDiv R x) := by
  nontriviality S
  have := congr_arg leadingCoeff (minpolyDiv_spec R x)
  rw [leadingCoeff_mul', ((minpoly.monic hx).map (algebraMap R S)).leadingCoeff] at this
  · simpa using! this
  · simpa using! minpolyDiv_ne_zero hx
/-
**natDegree_minpolyDiv_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natDegree_minpolyDiv_succ [Nontrivial S] : natDegree (minpolyDiv R x) + 1 
= natDegree (minpoly R x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用引理 `minpolyDiv_spec`：minpolyDiv_spec : minpolyDiv R x * (X - C x) = (minpoly
 R x).map (algebraMap R S)
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `minpolyDiv_ne_zero`：minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x !
= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_minpolyDiv_succ [Nontrivial S] :
    natDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x) := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap R S), ← minpolyDiv_spec, natDegree_mul']
  · simp
  · simpa using minpolyDiv_ne_zero hx
/-
**natDegree_minpolyDiv_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natDegree_minpolyDiv_lt [Nontrivial S] : natDegree (minpolyDiv R x) < natD
egree (minpoly R x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `natDegree_minpolyDiv_succ`：natDegree_minpolyDiv_succ [Nontrivial S] : na
tDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma natDegree_minpolyDiv_lt [Nontrivial S] :
    natDegree (minpolyDiv R x) < natDegree (minpoly R x) := by
  rw [← natDegree_minpolyDiv_succ hx]
  exact Nat.lt_succ_self _
/-
**minpolyDiv_eq_of_isIntegrallyClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpolyDiv_eq_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R] [I
sDomain S] [Algebra R K] [Algebra K S] [IsScalarTower R K S] [IsFractionRing R K
] : minpolyDiv R x = minpolyDiv K x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions'`：isIntegrallyClosed_eq_fi
eld_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S} (hs : Is
Integral R s) : minpoly K s = (minpo…
-/
lemma minpolyDiv_eq_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R K] [Algebra K S] [IsScalarTower R K S] [IsFractionRing R K] :
    minpolyDiv R x = minpolyDiv K x := by
  delta minpolyDiv
  rw [IsScalarTower.algebraMap_eq R K S, ← map_map,
    ← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx]
/-
**coeff_minpolyDiv_sub_pow_mem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeff_minpolyDiv_sub_pow_mem_span {i} (hi : i <= natDegree (minpolyDiv R x
)) : coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) - x ^ i in Submodul
e.span R ((x ^ ·) '' Set.Iio i)
参数：hi : i <= natDegree (minpolyDiv R x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `minpolyDiv_monic`：minpolyDiv_monic : Monic (minpolyDiv R x)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `coeff_minpolyDiv`：coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i = alge
braMap R S (coeff (minpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
（共 46 条，此处仅展示前 30 条）
-/
lemma coeff_minpolyDiv_sub_pow_mem_span {i} (hi : i ≤ natDegree (minpolyDiv R x)) :
    coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) - x ^ i ∈
      Submodule.span R ((x ^ ·) '' Set.Iio i) := by
  induction i with
  | zero => simp [(minpolyDiv_monic hx).leadingCoeff]
  | succ i IH =>
    rw [coeff_minpolyDiv, add_sub_assoc, pow_succ, ← sub_mul, Algebra.algebraMap_eq_smul_one]
    refine add_mem ?_ ?_
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨0, Nat.zero_lt_succ _, pow_zero _⟩
    · rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left (b := 1) hi)]
      apply SetLike.le_def.mp ?_
        (Submodule.mul_mem_mul (IH ((Nat.le_succ _).trans hi))
          (Submodule.mem_span_singleton_self x))
      rw [Submodule.span_mul_span, Set.mul_singleton, Set.image_image]
      apply Submodule.span_mono
      rintro _ ⟨j, hj, rfl⟩
      rw [Set.mem_Iio] at hj
      exact ⟨j + 1, Nat.add_lt_of_lt_sub hj, pow_succ x j⟩
/-
**span_coeff_minpolyDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：span_coeff_minpolyDiv : Submodule.span R (Set.range (coeff (minpolyDiv R x
))) = Subalgebra.toSubmodule (R[x])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `coeff_minpolyDiv_mem_adjoin`：coeff_minpolyDiv_mem_adjoin (x : S) (i) : c
oeff (minpolyDiv R x) i in R[x]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_range_natDegree_eq_adjoin`：Submodule.span_range_natDegree
_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A] {x : A} {f : R[X]} (hf 
: f.Monic) (hfx : aeval x f = …
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.sub_mem_iff_right`：sub_mem_iff_right (hx : x in p) : x - y in 
p ↔ y in p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `coeff_minpolyDiv_sub_pow_mem_span`：coeff_minpolyDiv_sub_pow_mem_span {i}
 (hi : i <= natDegree (minpolyDiv R x)) : coeff (minpolyDiv R x) (natDegree (min
polyDiv R x) - i) - x ^…
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用引理 `natDegree_minpolyDiv_succ`：natDegree_minpolyDiv_succ [Nontrivial S] : na
tDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x)
-/
lemma span_coeff_minpolyDiv :
    Submodule.span R (Set.range (coeff (minpolyDiv R x))) =
      Subalgebra.toSubmodule (R[x]) := by
  nontriviality S
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply coeff_minpolyDiv_mem_adjoin
  · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx) (minpoly.aeval _ _),
      Submodule.span_le]
    simp only [Finset.coe_image, Finset.coe_range, Set.image_subset_iff]
    intro i
    induction i using Nat.strongRecOn with | ind i hi => ?_
    intro hi'
    have : coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) ∈
        Submodule.span R (Set.range (coeff (minpolyDiv R x))) :=
      Submodule.subset_span (Set.mem_range_self _)
    rw [Set.mem_preimage, SetLike.mem_coe, ← Submodule.sub_mem_iff_right _ this]
    refine SetLike.le_def.mp ?_ (coeff_minpolyDiv_sub_pow_mem_span hx ?_)
    · rw [Submodule.span_le, Set.image_subset_iff]
      intro j (hj : j < i)
      exact hi j hj (lt_trans hj hi')
    · rwa [← natDegree_minpolyDiv_succ hx, Set.mem_Iio, Nat.lt_succ_iff] at hi'

end IsIntegral

/-
**natDegree_minpolyDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natDegree_minpolyDiv : natDegree (minpolyDiv R x) = natDegree (minpoly R x
) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.subsingleton`：subsingleton [Subsingleton B] : minpoly A x = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `natDegree_minpolyDiv_succ`：natDegree_minpolyDiv_succ [Nontrivial S] : na
tDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x)
· 使用引理 `minpolyDiv_eq_zero`：minpolyDiv_eq_zero (hx : ¬IsIntegral R x) : minpolyD
iv R x = 0
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
-/
lemma natDegree_minpolyDiv :
    natDegree (minpolyDiv R x) = natDegree (minpoly R x) - 1 := by
  nontriviality S
  by_cases hx : IsIntegral R x
  · rw [← natDegree_minpolyDiv_succ hx]; rfl
  · rw [minpolyDiv_eq_zero hx, minpoly.eq_zero hx]; rfl


section PowerBasis

variable {K}

/-
**sum_smul_minpolyDiv_eq_X_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_smul_minpolyDiv_eq_X_pow (E) [Field E] [Algebra K E] [IsAlgClosed E] [
FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L} (hxL : K[x] = ⊤) {r : N
at} (hr : r < finrank K L) : ∑ σ : L ->ₐ[K] E, ((x ^ r / aeval x (derivative <| 
minpoly K x)) • minpolyDiv K x).map σ = (X ^ r : E[X])
参数：E；hxL : K[x] = ⊤；hr : r < finrank K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `AlgHom.ext_of_adjoin_eq_top`：ext_of_adjoin_eq_top {s : Set A} (h : adjoi
n R s = ⊤) ⦃φ₁ φ₂ : A ->ₐ[R] B⦄ (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂
· 使用引理 `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`：eq_zero_of_natD
egree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R] (p : R[X]) {ι} [Fint
ype ι] {f : ι -> R} (hf : Function.Injective …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_smul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p 
: Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (r : R),   Polynomial.map f 
(r • p) =…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用引理 `eval₂_minpolyDiv_self`：eval₂_minpolyDiv_self {T} [CommRing T] [Algebra R
 T] [IsDomain T] [DecidableEq T] (x : S) (σ₁ σ₂ : S ->ₐ[R] T) : eval₂ σ₁ (σ₂ x) 
(minpolyDiv…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
（共 67 条，此处仅展示前 30 条）
-/
lemma sum_smul_minpolyDiv_eq_X_pow (E) [Field E] [Algebra K E] [IsAlgClosed E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {x : L} (hxL : K[x] = ⊤) {r : ℕ} (hr : r < finrank K L) :
    ∑ σ : L →ₐ[K] E, ((x ^ r / aeval x (derivative <| minpoly K x)) •
      minpolyDiv K x).map σ = (X ^ r : E[X]) := by
  classical
  rw [← sub_eq_zero]
  have : Function.Injective (fun σ : L →ₐ[K] E ↦ σ x) := fun _ _ h =>
    AlgHom.ext_of_adjoin_eq_top hxL (fun _ hx ↦ hx ▸ h)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ this
  · intro σ
    simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, eval_sub, eval_finsetSum,
      eval_smul, eval_map, eval₂_minpolyDiv_self, this.eq_iff, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, eval_X_pow]
    rw [sub_eq_zero, div_mul_cancel₀]
    rw [ne_eq, map_eq_zero_iff σ σ.toRingHom.injective]
    exact (IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · refine (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt ((Polynomial.natDegree_sum_le _ _).trans_lt ?_) ?_)
    · simp only [Polynomial.map_smul,
        map_div₀, map_pow, RingHom.coe_coe, Function.comp_apply,
        Finset.mem_univ, forall_true_left, Finset.fold_max_lt, AlgHom.card]
      refine ⟨finrank_pos, ?_⟩
      intro σ
      exact ((Polynomial.natDegree_smul_le _ _).trans natDegree_map_le).trans_lt
        ((natDegree_minpolyDiv_lt (Algebra.IsIntegral.isIntegral x)).trans_le
          (minpoly.natDegree_le _))
    · rwa [natDegree_pow, natDegree_X, mul_one, AlgHom.card]

end PowerBasis

