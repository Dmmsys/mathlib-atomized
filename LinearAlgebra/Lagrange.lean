/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `s : Finset ι` is a finite set of indices, with `v : ι → F` an
  indexing of the field over some type. We call the image of `v` on `s` the interpolation nodes,
  though strictly unique nodes are only defined when `v` is injective on `s`.
* `Lagrange.basisDivisor x y`, with `x y : F`. These are the normalised irreducible factors of
  the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
  are distinct.
* `Lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
  and `0` at `v j` for `i ≠ j`.
* `Lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
  Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
  associated with the _nodes_ `x i`.
-/

@[expose] public section


open Polynomial

section PolynomialDetermination

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype
open scoped Finset

variable (s : Finset R)

/-
**Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s) 
(eval_f : forall x in s, f.eval x = 0) : f = 0
参数：degree_f_lt : f.degree < #s；eval_f : forall x in s, f.eval x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Polynomial.degreeLTEquiv_eq_zero_iff_eq_zero`：degreeLTEquiv_eq_zero_iff_
eq_zero {n : Nat} {p : R[X]} (hp : p in degreeLT R n) : degreeLTEquiv _ _ ⟨p, hp
⟩ = 0 ↔ p = 0
· 使用定理 `Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero`：eq_zero_of_forall_in
dex_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n -> R} (hf : Function.Injective
 f) (hfv : forall j, (∑ i, v i * f j ^ (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_eq_sum_degreeLTEquiv`：eval_eq_sum_degreeLTEquiv {n : Nat
} {p : R[X]} (hp : p in degreeLT R n) (x : R) : p.eval x = ∑ i, degreeLTEquiv _ 
_ ⟨p, hp⟩ i * x ^ (i : Nat…
· 使用定理 `Finset.coe_mem`：coe_mem {s : Finset α} (x : (s : Set α)) : ↑x in s
-/
theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s)
    (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 := by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)
/-
**Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
 (eval_fg : forall x in s, f.eval x = g.eval x) : f = g
参数：degree_fg_lt : (f - g).degree < #s；eval_fg : forall x in s, f.eval x = g.eval
 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero`：eq_zero_of_degre
e_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s) (eval_f : forall x in 
s, f.eval x = 0) : f = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
    (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg
/-
**Polynomial.eq_of_degrees_lt_of_eval_finset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s) (degree_g
_lt : g.degree < #s) (eval_fg : forall x in s, f.eval x = g.eval x) : f = g
参数：degree_f_lt : f.degree < #s；degree_g_lt : g.degree < #s；eval_fg : forall x in
 s, f.eval x = g.eval x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq`：eq_of_degree_sub_lt_of
_eval_finset_eq (degree_fg_lt : (f - g).degree < #s) (eval_fg : forall x in s, f
.eval x = g.eval x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
-/
theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

/--
Two polynomials, with the same degree and leading coefficient, which have the same evaluation
on a set of distinct values with cardinality equal to the degree, are equal.
-/
/-
**Polynomial.eq_of_degree_le_of_eval_finset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：eq_of_degree_le_of_eval_finset_eq (h_deg_le : f.degree <= #s) (h_deg_eq : 
f.degree = g.degree) (hlc : f.leadingCoeff = g.leadingCoeff) (h_eval : forall x 
in s, f.eval x = g.eval x) : f = g
参数：h_deg_le : f.degree <= #s；h_deg_eq : f.degree = g.degree；hlc : f.leadingCoeff
 = g.leadingCoeff；h_eval : forall x in s, f.eval x = g.eval x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq`：eq_of_degree_sub_lt_of
_eval_finset_eq (degree_fg_lt : (f - g).degree < #s) (eval_fg : forall x in s, f
.eval x = g.eval x) : f = g
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p

--- 原说明 ---
Two polynomials, with the same degree and leading coefficient, which have the sa
me evaluation
on a set of distinct values with cardinality equal to the degree, are equal.
-/
theorem eq_of_degree_le_of_eval_finset_eq
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ x ∈ s, f.eval x = g.eval x) :
    f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le) h_eval

end Finset

section Indexed

open Finset

variable {ι : Type*} {v : ι → R} (s : Finset ι)

/-
**Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s) (degree_f
_lt : f.degree < #s) (eval_f : forall i in s, f.eval (v i) = 0) : f = 0
参数：hvs : Set.InjOn v s；degree_f_lt : f.degree < #s；eval_f : forall i in s, f.eva
l (v i) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero`：eq_zero_of_degre
e_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s) (eval_f : forall x in 
s, f.eval x = 0) : f = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < #s) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj
/-
**Polynomial.eq_of_degree_sub_lt_of_eval_index_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_fg_lt :
 (f - g).degree < #s) (eval_fg : forall i in s, f.eval (v i) = g.eval (v i)) : f
 = g
参数：hvs : Set.InjOn v s；degree_fg_lt : (f - g).degree < #s；eval_fg : forall i in 
s, f.eval (v i) = g.eval (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero`：eq_zero_of_degree
_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) (e
val_f : forall i in s, f.eval (v i) = 0) : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg
/-
**Polynomial.eq_of_degrees_lt_of_eval_index_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.d
egree < #s) (degree_g_lt : g.degree < #s) (eval_fg : forall i in s, f.eval (v i)
 = g.eval (v i)) : f = g
参数：hvs : Set.InjOn v s；degree_f_lt : f.degree < #s；degree_g_lt : g.degree < #s；e
val_fg : forall i in s, f.eval (v i) = g.eval (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq`：eq_of_degree_sub_lt_of_
eval_index_eq (hvs : Set.InjOn v s) (degree_fg_lt : (f - g).degree < #s) (eval_f
g : forall i in s, f.eval (v i) = g.e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
-/
theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt
/-
**Polynomial.eq_of_degree_le_of_eval_index_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s) (h_deg_le : f.degre
e <= #s) (h_deg_eq : f.degree = g.degree) (hlc : f.leadingCoeff = g.leadingCoeff
) (h_eval : forall i in s, f.eval (v i) = g.eval (v i)) : f = g
参数：hvs : Set.InjOn v s；h_deg_le : f.degree <= #s；h_deg_eq : f.degree = g.degree；
hlc : f.leadingCoeff = g.leadingCoeff；h_eval : forall i in s, f.eval (v i) = g.e
val (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq`：eq_of_degree_sub_lt_of_
eval_index_eq (hvs : Set.InjOn v s) (degree_fg_lt : (f - g).degree < #s) (eval_f
g : forall i in s, f.eval (v i) = g.e…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p
-/
theorem eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s)
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le)
      h_eval

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

section BasisDivisor
variable {F : Type*} [Field F]
variable {x y : F}

/-- `basisDivisor x y` is the unique linear or constant polynomial such that
when evaluated at `x` it gives `1` and `y` it gives `0` (where when `x = y` it is identically `0`).
Such polynomials are the building blocks for the Lagrange interpolants. -/
/-
**Lagrange.basisDivisor** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor (x y : F) : F[X]
参数：x y : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`basisDivisor x y` is the unique linear or constant polynomial such that
when evaluated at `x` it gives `1` and `y` it gives `0` (where when `x = y` it i
s identically `0`).
Such polynomials are the building blocks for the Lagrange interpolants.
-/
def basisDivisor (x y : F) : F[X] :=
  C (x - y)⁻¹ * (X - C y)
/-
**Lagrange.basisDivisor_self** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor_self : basisDivisor x x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisDivisor_self : basisDivisor x x = 0 := by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]
/-
**Lagrange.basisDivisor_inj** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y
参数：hxy : basisDivisor x y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y := by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy

@[simp]
/-
**Lagrange.basisDivisor_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor_eq_zero_iff : basisDivisor x y = 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Lagrange.basisDivisor_inj`：basisDivisor_inj (hxy : basisDivisor x y = 0)
 : x = y
· 使用定理 `Lagrange.basisDivisor_self`：basisDivisor_self : basisDivisor x x = 0
-/
theorem basisDivisor_eq_zero_iff : basisDivisor x y = 0 ↔ x = y :=
  ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩
/-
**Lagrange.basisDivisor_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor_ne_zero_iff : basisDivisor x y != 0 ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Lagrange.basisDivisor_eq_zero_iff`：basisDivisor_eq_zero_iff : basisDivis
or x y = 0 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem basisDivisor_ne_zero_iff : basisDivisor x y ≠ 0 ↔ x ≠ y := by
  rw [Ne, basisDivisor_eq_zero_iff]
/-
**Lagrange.degree_basisDivisor_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_basisDivisor_of_ne (hxy : x != y) : (basisDivisor x y).degree = 1
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basisDivisor.eq_1`：∀ {F : Type u_1} [inst : Field F] (x y : F),
   Lagrange.basisDivisor x y = Polynomial.C (x - y)⁻¹ * (Polynomial.X - Polynomi
al.C y)
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem degree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).degree = 1 := by
  rw [basisDivisor, degree_mul, degree_X_sub_C, degree_C, zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)

@[simp]
/-
**Lagrange.degree_basisDivisor_self** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_basisDivisor_self : (basisDivisor x x).degree = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basisDivisor_self`：basisDivisor_self : basisDivisor x x = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
-/
theorem degree_basisDivisor_self : (basisDivisor x x).degree = ⊥ := by
  rw [basisDivisor_self, degree_zero]
/-
**Lagrange.natDegree_basisDivisor_self** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：natDegree_basisDivisor_self : (basisDivisor x x).natDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basisDivisor_self`：basisDivisor_self : basisDivisor x x = 0
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
-/
theorem natDegree_basisDivisor_self : (basisDivisor x x).natDegree = 0 := by
  rw [basisDivisor_self, natDegree_zero]
/-
**Lagrange.natDegree_basisDivisor_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：natDegree_basisDivisor_of_ne (hxy : x != y) : (basisDivisor x y).natDegree
 = 1
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Lagrange.degree_basisDivisor_of_ne`：degree_basisDivisor_of_ne (hxy : x !
= y) : (basisDivisor x y).degree = 1
-/
theorem natDegree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)

@[simp]
/-
**Lagrange.eval_basisDivisor_right** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_basisDivisor_right : eval y (basisDivisor x y) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_basisDivisor_right : eval y (basisDivisor x y) = 0 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]
/-
**Lagrange.eval_basisDivisor_left_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_basisDivisor_left_of_ne (hxy : x != y) : eval x (basisDivisor x y) = 
1
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
-/
theorem eval_basisDivisor_left_of_ne (hxy : x ≠ y) : eval x (basisDivisor x y) = 1 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero_of_ne hxy)

end BasisDivisor

section Basis

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i j : ι}

open Finset

/-- Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `v i` for a
map `v : ι → F`. For `i, j ∈ s`, `basis s v i` evaluates to 0 at `v j` for `i ≠ j`. When
`v` is injective on `s`, `basis s v i` evaluates to 1 at `v i`. -/
/-
**Lagrange.basis** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：{F : Type u_1} → [inst : Field F] → {ι : Type u_2} → [DecidableEq ι] → Fin
set ι → (ι → F) → ι → Polynomial F
参数：ι → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `v i` for
 a
map `v : ι → F`. For `i, j ∈ s`, `basis s v i` evaluates to 0 at `v j` for `i ≠ 
j`. When
`v` is injective on `s`, `basis s v i` evaluates to 1 at `v i`.
-/
protected def basis (s : Finset ι) (v : ι → F) (i : ι) : F[X] :=
  ∏ j ∈ s.erase i, basisDivisor (v i) (v j)

@[simp]
/-
**Lagrange.basis_empty** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basis_empty : Lagrange.basis ∅ v i = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basis_empty : Lagrange.basis ∅ v i = 1 :=
  rfl

@[simp]
/-
**Lagrange.basis_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basis_singleton (i : ι) : Lagrange.basis {i} v i = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basis.eq_1`：∀ {F : Type u_1} [inst : Field F] {ι : Type u_2} [i
nst_1 : DecidableEq ι] (s : Finset ι) (v : ι → F) (i : ι),   Lagrange.basis s v 
i = ∏ j ∈…
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
-/
theorem basis_singleton (i : ι) : Lagrange.basis {i} v i = 1 := by
  rw [Lagrange.basis, erase_singleton, prod_empty]

@[simp]
/-
**Lagrange.basis_pair_left** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basis_pair_left (hij : i != j) : Lagrange.basis {i, j} v i = basisDivisor 
(v i) (v j)
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_pair_left (hij : i ≠ j) : Lagrange.basis {i, j} v i = basisDivisor (v i) (v j) := by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_notMem, mem_singleton,
    not_false_iff, prod_singleton]

@[simp]
/-
**Lagrange.basis_pair_right** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basis_pair_right (hij : i != j) : Lagrange.basis {i, j} v j = basisDivisor
 (v j) (v i)
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pair_comm`：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
· 使用定理 `Lagrange.basis_pair_left`：basis_pair_left (hij : i != j) : Lagrange.basi
s {i, j} v i = basisDivisor (v i) (v j)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem basis_pair_right (hij : i ≠ j) : Lagrange.basis {i, j} v j = basisDivisor (v j) (v i) := by
  rw [pair_comm]
  exact basis_pair_left hij.symm
/-
**Lagrange.basis_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basis_ne_zero (hvs : Set.InjOn v s) (hi : i in s) : Lagrange.basis s v i !
= 0
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basisDivisor_eq_zero_iff`：basisDivisor_eq_zero_iff : basisDivis
or x y = 0 ↔ x = y
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem basis_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : Lagrange.basis s v i ≠ 0 := by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basisDivisor_eq_zero_iff, hvs.eq_iff hi hj]
  exact hij.symm

@[simp]
/-
**Lagrange.eval_basis_self** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_basis_self (hvs : Set.InjOn v s) (hi : i in s) : (Lagrange.basis s v 
i).eval (v i) = 1
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.basis.eq_1`：∀ {F : Type u_1} [inst : Field F] {ι : Type u_2} [i
nst_1 : DecidableEq ι] (s : Finset ι) (v : ι → F) (i : ι),   Lagrange.basis s v 
i = ∏ j ∈…
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `Lagrange.eval_basisDivisor_left_of_ne`：eval_basisDivisor_left_of_ne (hxy
 : x != y) : eval x (basisDivisor x y) = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem eval_basis_self (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).eval (v i) = 1 := by
  rw [Lagrange.basis, eval_prod]
  refine prod_eq_one fun j H => ?_
  rw [eval_basisDivisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm

@[simp]
/-
**Lagrange.eval_basis_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_basis_of_ne (hij : i != j) (hj : j in s) : (Lagrange.basis s v i).eva
l (v j) = 0
参数：hij : i != j；hj : j in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Lagrange.eval_basisDivisor_right`：eval_basisDivisor_right : eval y (basi
sDivisor x y) = 0
-/
theorem eval_basis_of_ne (hij : i ≠ j) (hj : j ∈ s) : (Lagrange.basis s v i).eval (v j) = 0 := by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basisDivisor_right⟩⟩

@[simp]
/-
**Lagrange.natDegree_basis** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：natDegree_basis (hvs : Set.InjOn v s) (hi : i in s) : (Lagrange.basis s v 
i).natDegree = #s - 1
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Lagrange.natDegree_basisDivisor_of_ne`：natDegree_basisDivisor_of_ne (hxy
 : x != y) : (basisDivisor x y).natDegree = 1
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Lagrange.basisDivisor_eq_zero_iff`：basisDivisor_eq_zero_iff : basisDivis
or x y = 0 ↔ x = y
· 使用定理 `Polynomial.natDegree_prod`：natDegree_prod (h : forall i in s, f i != 0) 
: (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem natDegree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree = #s - 1 := by
  have H : ∀ j, j ∈ s.erase i → basisDivisor (v i) (v j) ≠ 0 := by
    simp_rw [Ne, mem_erase, basisDivisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi, card_eq_sum_ones]
  convert! natDegree_prod _ _ H using 1
  refine sum_congr rfl fun j hj => (natDegree_basisDivisor_of_ne ?_).symm
  rw [Ne, ← basisDivisor_eq_zero_iff]
  exact H _ hj
/-
**Lagrange.degree_basis** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_basis (hvs : Set.InjOn v s) (hi : i in s) : (Lagrange.basis s v i).
degree = ↑(#s - 1)
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Lagrange.basis_ne_zero`：basis_ne_zero (hvs : Set.InjOn v s) (hi : i in s
) : Lagrange.basis s v i != 0
· 使用定理 `Lagrange.natDegree_basis`：natDegree_basis (hvs : Set.InjOn v s) (hi : i 
in s) : (Lagrange.basis s v i).natDegree = #s - 1
-/
theorem degree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).degree = ↑(#s - 1) := by
  rw [degree_eq_natDegree (basis_ne_zero hvs hi), natDegree_basis hvs hi]
/-
**Lagrange.sum_basis** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) : ∑ j in s, Lagrange.bas
is s v j = 1
参数：hvs : Set.InjOn v s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_degrees_lt_of_eval_index_eq`：eq_of_degrees_lt_of_eval_i
ndex_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) (degree_g_lt : g.deg
ree < #s) (eval_fg : forall i in s…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Lagrange.degree_basis`：degree_basis (hvs : Set.InjOn v s) (hi : i in s) 
: (Lagrange.basis s v i).degree = ↑(#s - 1)
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `Finset.card_ne_zero_of_mem`：card_ne_zero_of_mem (h : a in s) : #s != 0
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Lagrange.eval_basis_self`：eval_basis_self (hvs : Set.InjOn v s) (hi : i 
in s) : (Lagrange.basis s v i).eval (v i) = 1
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Lagrange.eval_basis_of_ne`：eval_basis_of_ne (hij : i != j) (hj : j in s)
 : (Lagrange.basis s v i).eval (v j) = 0
-/
theorem sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ j ∈ s, Lagrange.basis s v j = 1 := by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i hi
    rw [degree_basis hvs hi, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finsetSum, eval_one, ← add_sum_erase _ _ hi, eval_basis_self hvs hi,
      add_eq_left]
    refine sum_eq_zero fun j hj => ?_
    rcases mem_erase.mp hj with ⟨hij, _⟩
    rw [eval_basis_of_ne hij hi]
/-
**Lagrange.basisDivisor_add_symm** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：basisDivisor_add_symm {x y : F} (hxy : x != y) : basisDivisor x y + basisD
ivisor y x = 1
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.sum_basis`：sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) : 
∑ j in s, Lagrange.basis s v j = 1
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Lagrange.basis_pair_left`：basis_pair_left (hij : i != j) : Lagrange.basi
s {i, j} v i = basisDivisor (v i) (v j)
· 使用定理 `Lagrange.basis_pair_right`：basis_pair_right (hij : i != j) : Lagrange.ba
sis {i, j} v j = basisDivisor (v j) (v i)
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem basisDivisor_add_symm {x y : F} (hxy : x ≠ y) :
    basisDivisor x y + basisDivisor y x = 1 := by
  classical
  rw [← sum_basis Function.injective_id.injOn ⟨x, mem_insert_self _ {y}⟩,
    sum_insert (notMem_singleton.mpr hxy), sum_singleton, basis_pair_left hxy,
    basis_pair_right hxy, id, id]
/-
**Lagrange.leadingCoeff_basis** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：leadingCoeff_basis (hvs : Set.InjOn v s) (hi : i in s) : (Lagrange.basis s
 v i).leadingCoeff = (∏ j in s.erase i, ((v i) - (v j)))⁻¹
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_finsetProd_X_sub_C_eq_card`：∀ {R : Type u} [inst : 
CommRing R] [Nontrivial R] {α : Type u_1} (s : Finset α) (f : α → R),   (∏ a ∈ s
, (Polynomial.X - Polynomial.C (f a))…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `Polynomial.monic_prod_X_sub_C`：monic_prod_X_sub_C {α : Type*} (b : α -> 
R) (s : Finset α) : Monic (∏ a in s, (X - C (b a)))
· 使用定理 `Lagrange.natDegree_basis`：natDegree_basis (hvs : Set.InjOn v s) (hi : i 
in s) : (Lagrange.basis s v i).natDegree = #s - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).leadingCoeff = (∏ j ∈ s.erase i, ((v i) - (v j)))⁻¹ := by
  have : (∏ j ∈ s.erase i, (X - C (v j))).coeff (#s - 1) = 1 := by
    simpa [hi] using (monic_prod_X_sub_C v (s.erase i)).coeff_natDegree
  simp_rw [leadingCoeff, natDegree_basis hvs hi, Lagrange.basis]
  simp [basisDivisor, Finset.prod_mul_distrib, ← map_prod, this]

end Basis

section Interpolate

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s t : Finset ι} {i j : ι} {v : ι → F} (r r' : ι → F)

open Finset

/-- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. -/
@[simps]
/-
**Lagrange.interpolate** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：interpolate (s : Finset ι) (v : ι -> F) : (ι -> F) ->ₗ[F] F[X] where toFun
 r
参数：s : Finset ι；v : ι -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` i
njective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`.
-/
def interpolate (s : Finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X] where
  toFun r := ∑ i ∈ s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
/-
**Lagrange.interpolate_empty** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_empty : interpolate ∅ v r = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
-/
theorem interpolate_empty : interpolate ∅ v r = 0 := by rw [interpolate_apply, sum_empty]
/-
**Lagrange.interpolate_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_singleton : interpolate {i} v r = C (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Lagrange.basis_singleton`：basis_singleton (i : ι) : Lagrange.basis {i} v
 i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem interpolate_singleton : interpolate {i} v r = C (r i) := by
  rw [interpolate_apply, sum_singleton, basis_singleton, mul_one]
/-
**Lagrange.interpolate_one** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_one (hvs : Set.InjOn v s) (hs : s.Nonempty) : interpolate s v 
1 = 1
参数：hvs : Set.InjOn v s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Lagrange.sum_basis`：sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) : 
∑ j in s, Lagrange.basis s v j = 1
-/
theorem interpolate_one (hvs : Set.InjOn v s) (hs : s.Nonempty) : interpolate s v 1 = 1 := by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs
/-
**Lagrange.eval_interpolate_at_node** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_interpolate_at_node (hvs : Set.InjOn v s) (hi : i in s) : eval (v i) 
(interpolate s v r) = r i
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Lagrange.eval_basis_self`：eval_basis_self (hvs : Set.InjOn v s) (hi : i 
in s) : (Lagrange.basis s v i).eval (v i) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Lagrange.eval_basis_of_ne`：eval_basis_of_ne (hij : i != j) (hj : j in s)
 : (Lagrange.basis s v i).eval (v j) = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem eval_interpolate_at_node (hvs : Set.InjOn v s) (hi : i ∈ s) :
    eval (v i) (interpolate s v r) = r i := by
  rw [interpolate_apply, eval_finsetSum, ← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi, mul_zero]
/-
**Lagrange.degree_interpolate_le** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_interpolate_le (hvs : Set.InjOn v s) : (interpolate s v r).degree <
= ↑(#s - 1)
参数：hvs : Set.InjOn v s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Lagrange.degree_basis`：degree_basis (hvs : Set.InjOn v s) (hi : i in s) 
: (Lagrange.basis s v i).degree = ↑(#s - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem degree_interpolate_le (hvs : Set.InjOn v s) :
    (interpolate s v r).degree ≤ ↑(#s - 1) := by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul, degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]
/-
**Lagrange.degree_interpolate_lt** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_interpolate_lt (hvs : Set.InjOn v s) : (interpolate s v r).degree <
 #s
参数：hvs : Set.InjOn v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Lagrange.interpolate_empty`：interpolate_empty : interpolate ∅ v r = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Lagrange.degree_interpolate_le`：degree_interpolate_le (hvs : Set.InjOn v
 s) : (interpolate s v r).degree <= ↑(#s - 1)
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem degree_interpolate_lt (hvs : Set.InjOn v s) : (interpolate s v r).degree < #s := by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _ hvs) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one
/-
**Lagrange.degree_interpolate_erase_lt** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_interpolate_erase_lt (hvs : Set.InjOn v s) (hi : i in s) : (interpo
late (s.erase i) v r).degree < ↑(#s - 1)
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Lagrange.degree_interpolate_lt`：degree_interpolate_lt (hvs : Set.InjOn v
 s) : (interpolate s v r).degree < #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
-/
theorem degree_interpolate_erase_lt (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (interpolate (s.erase i) v r).degree < ↑(#s - 1) := by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)
/-
**Lagrange.values_eq_on_of_interpolate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：values_eq_on_of_interpolate_eq (hvs : Set.InjOn v s) (hrr' : interpolate s
 v r = interpolate s v r') : forall i in s, r i = r' i
参数：hvs : Set.InjOn v s；hrr' : interpolate s v r = interpolate s v r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.eval_interpolate_at_node`：eval_interpolate_at_node (hvs : Set.I
njOn v s) (hi : i in s) : eval (v i) (interpolate s v r) = r i
-/
theorem values_eq_on_of_interpolate_eq (hvs : Set.InjOn v s)
    (hrr' : interpolate s v r = interpolate s v r') : ∀ i ∈ s, r i = r' i := fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi, hrr', eval_interpolate_at_node r' hvs hi]
/-
**Lagrange.interpolate_eq_of_values_eq_on** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_eq_of_values_eq_on (hrr' : forall i in s, r i = r' i) : interp
olate s v r = interpolate s v r'
参数：hrr' : forall i in s, r i = r' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem interpolate_eq_of_values_eq_on (hrr' : ∀ i ∈ s, r i = r' i) :
    interpolate s v r = interpolate s v r' :=
  sum_congr rfl fun i hi => by rw [hrr' _ hi]
/-
**Lagrange.interpolate_eq_iff_values_eq_on** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_eq_iff_values_eq_on (hvs : Set.InjOn v s) : interpolate s v r 
= interpolate s v r' ↔ forall i in s, r i = r' i
参数：hvs : Set.InjOn v s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Lagrange.values_eq_on_of_interpolate_eq`：values_eq_on_of_interpolate_eq 
(hvs : Set.InjOn v s) (hrr' : interpolate s v r = interpolate s v r') : forall i
 in s, r i = r' i
· 使用定理 `Lagrange.interpolate_eq_of_values_eq_on`：interpolate_eq_of_values_eq_on 
(hrr' : forall i in s, r i = r' i) : interpolate s v r = interpolate s v r'
-/
theorem interpolate_eq_iff_values_eq_on (hvs : Set.InjOn v s) :
    interpolate s v r = interpolate s v r' ↔ ∀ i ∈ s, r i = r' i :=
  ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩
/-
**Lagrange.eq_interpolate** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < 
#s) : f = interpolate s v fun i => f.eval (v i)
参数：hvs : Set.InjOn v s；degree_f_lt : f.degree < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_degrees_lt_of_eval_index_eq`：eq_of_degrees_lt_of_eval_i
ndex_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) (degree_g_lt : g.deg
ree < #s) (eval_fg : forall i in s…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Lagrange.degree_interpolate_lt`：degree_interpolate_lt (hvs : Set.InjOn v
 s) : (interpolate s v r).degree < #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.eval_interpolate_at_node`：eval_interpolate_at_node (hvs : Set.I
njOn v s) (hi : i in s) : eval (v i) (interpolate s v r) = r i
-/
theorem eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) :
    f = interpolate s v fun i => f.eval (v i) :=
  eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun _ hi =>
    (eval_interpolate_at_node (fun x ↦ eval (v x) f) hvs hi).symm
/-
**Lagrange.eq_interpolate_of_eval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : 
f.degree < #s) (eval_f : forall i in s, f.eval (v i) = r i) : f = interpolate s 
v r
参数：hvs : Set.InjOn v s；degree_f_lt : f.degree < #s；eval_f : forall i in s, f.eva
l (v i) = r i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eq_interpolate`：eq_interpolate {f : F[X]} (hvs : Set.InjOn v s)
 (degree_f_lt : f.degree < #s) : f = interpolate s v fun i => f.eval (v i)
· 使用定理 `Lagrange.interpolate_eq_of_values_eq_on`：interpolate_eq_of_values_eq_on 
(hrr' : forall i in s, r i = r' i) : interpolate s v r = interpolate s v r'
-/
theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (eval_f : ∀ i ∈ s, f.eval (v i) = r i) : f = interpolate s v r := by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

/-- This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < Fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
/-
**Lagrange.eq_interpolate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) : (f.degree < #s ∧ for
all i in s, eval (v i) f = r i) ↔ f = interpolate s v r
参数：hvs : Set.InjOn v s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Lagrange.eq_interpolate_of_eval_eq`：eq_interpolate_of_eval_eq {f : F[X]}
 (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) (eval_f : forall i in s, f.
eval (v i) = r i) : f = …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.degree_interpolate_lt`：degree_interpolate_lt (hvs : Set.InjOn v
 s) : (interpolate s v r).degree < #s
· 使用定理 `Lagrange.eval_interpolate_at_node`：eval_interpolate_at_node (hvs : Set.I
njOn v s) (hi : i in s) : eval (v i) (interpolate s v r) = r i

--- 原说明 ---
This is the characteristic property of the interpolation: the interpolation is t
he
unique polynomial of `degree < Fintype.card ι` which takes the value of the `r i
` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) :
    (f.degree < #s ∧ ∀ i ∈ s, eval (v i) f = r i) ↔ f = interpolate s v r := by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩

/-- Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `Fintype.card ι`. -/
/-
**Lagrange.funEquivDegreeLT** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s -> F where 
toFun f i
参数：hvs : Set.InjOn v s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `Fintype.card ι`.
-/
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s → F where
  toFun f i := f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
  map_smul' c f := funext <| by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x ∈ s then r ⟨x, hx⟩ else 0,
      mem_degreeLT.2 <| degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi
/-
**Lagrange.interpolate_eq_sum_interpolate_insert_sdiff** 是 Mathlib 中的一个定理，位于命名空间
 `Lagrange`。
形式化陈述：interpolate_eq_sum_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.
Nonempty) (hst : s subseteq t) : interpolate t v r = ∑ i in s, interpolate (inse
rt i (t \ s)) v r * Lagrange.basis s v i
参数：hvt : Set.InjOn v t；hs : s.Nonempty；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.eq_interpolate_of_eval_eq`：eq_interpolate_of_eval_eq {f : F[X]}
 (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) (eval_f : forall i in s, f.
eval (v i) = r i) : f = …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `tsub_add_tsub_cancel`：tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b)
 : a - b + (b - c) = a - c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.succ_add_sub_one`：∀ (n m : ℕ), m.succ + n - 1 = m + n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Lagrange.degree_basis`：degree_basis (hvs : Set.InjOn v s) (hi : i in s) 
: (Lagrange.basis s v i).degree = ↑(#s - 1)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `WithBot.add_lt_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hBot α} [inst_1 : LT α] [AddRightStrictMono α] [AddRightReflectLT α],   z ≠ ⊥ → 
(x + z < y + z ↔ x…
（共 65 条，此处仅展示前 30 条）
-/
theorem interpolate_eq_sum_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.Nonempty)
    (hst : s ⊆ t) :
    interpolate t v r = ∑ i ∈ s, interpolate (insert i (t \ s)) v r * Lagrange.basis s v i := by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i hi
    have hs : 1 ≤ #s := Nonempty.card_pos ⟨_, hi⟩
    have hst' : #s ≤ #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc, tsub_add_tsub_cancel hst' hs, ← add_tsub_assoc_of_le (hs.trans hst'),
        Nat.succ_add_sub_one, zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi, H, WithBot.coe_add, Nat.cast_withBot,
      WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert!
      degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hst hi, sdiff_subset⟩)))
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right hi), card_sdiff_of_subset hst, add_comm]
  · simp_rw [eval_finsetSum, eval_mul]
    by_cases hi' : i ∈ s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hi, sdiff_subset⟩)))
          (mem_insert_self _ _),
        mul_one, add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rcases mem_erase.mp hj with ⟨hij, _⟩
      rw [eval_basis_of_ne hij hi', mul_zero]
    · have H : (∑ j ∈ s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finsetSum, sum_basis (hvt.mono hst) hs, eval_one]
      rw [← mul_one (r i), ← H, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset_iff.mpr ⟨hst hj, sdiff_subset⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))
/-
**Lagrange.interpolate_eq_add_interpolate_erase** 是 Mathlib 中的一个定理，位于命名空间 `Lagra
nge`。
形式化陈述：interpolate_eq_add_interpolate_erase (hvs : Set.InjOn v s) (hi : i in s) (
hj : j in s) (hij : i != j) : interpolate s v r = interpolate (s.erase j) v r * 
basisDivisor (v i) (v j) + interpolate (s.erase i) v r * basisDivisor (v j) (v i
)
参数：hvs : Set.InjOn v s；hi : i in s；hj : j in s；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_eq_sum_interpolate_insert_sdiff`：interpolate_eq_sum
_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.Nonempty) (hst : s subse
teq t) : interpolate t v r = ∑ i in s, int…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Lagrange.basis_pair_left`：basis_pair_left (hij : i != j) : Lagrange.basi
s {i, j} v i = basisDivisor (v i) (v j)
· 使用定理 `Lagrange.basis_pair_right`：basis_pair_right (hij : i != j) : Lagrange.ba
sis {i, j} v j = basisDivisor (v j) (v i)
· 使用定理 `Finset.sdiff_insert_insert_of_mem_of_notMem`：sdiff_insert_insert_of_mem_
of_notMem {s t : Finset α} {x : α} (hxs : x in s) (hxt : x ∉ t) : insert x (s \ 
insert x t) = s \ t
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.pair_comm`：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem interpolate_eq_add_interpolate_erase (hvs : Set.InjOn v s) (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    interpolate s v r =
      interpolate (s.erase j) v r * basisDivisor (v i) (v j) +
        interpolate (s.erase i) v r * basisDivisor (v j) (v i) := by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i, mem_insert_self i {j}⟩ _,
    sum_insert (notMem_singleton.mpr hij), sum_singleton, basis_pair_left hij,
    basis_pair_right hij, sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij),
    sdiff_singleton_eq_erase, pair_comm,
    sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm),
    sdiff_singleton_eq_erase]
  exact insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩
/-
**Lagrange.interpolate_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_eq_sum : interpolate s v r = ∑ i in s, C (r i / ∏ j in s.erase
 i, (v i - v j)) * (∏ j in s.erase i, (X - C (v j)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interpolate_eq_sum : interpolate s v r =
    ∑ i ∈ s, C (r i / ∏ j ∈ s.erase i, (v i - v j)) * (∏ j ∈ s.erase i, (X - C (v j))) := by
  simp [Lagrange.basis, basisDivisor, div_eq_mul_inv, prod_mul_distrib, ← map_prod,
    ← prod_inv_distrib, mul_assoc]
/-
**Lagrange.iterate_derivative_interpolate** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：iterate_derivative_interpolate (hvs : Set.InjOn v s) {k : Nat} (hk : k < #
s) : derivative^[k] (interpolate s v r) = k.factorial * ∑ i in s, C (r i / ∏ j i
n s.erase i, (v i - v j)) * ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a 
in t, (X - C (v a))
参数：hvs : Set.InjOn v s；hk : k < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_eq_sum`：interpolate_eq_sum : interpolate s v r = ∑ 
i in s, C (r i / ∏ j in s.erase i, (v i - v j)) * (∏ j in s.erase i, (X - C (v j
)))
· 使用定理 `Polynomial.iterate_derivative_sum`：iterate_derivative_sum (k : Nat) (s :
 Finset ι) (f : ι -> R[X]) : derivative^[k] (∑ b in s, f b) = ∑ b in s, derivati
ve^[k] (f b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.iterate_derivative_C_mul`：iterate_derivative_C_mul (a : R) (p
 : R[X]) (k : Nat) : derivative^[k] (C a * p) = C a * derivative^[k] p
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Finset.powersetCard_eq_filter`：powersetCard_eq_filter {n} {s : Finset α}
 : powersetCard n s = (powerset s).filter fun x => x.card = n
· 使用定理 `Finset.powerset_image`：powerset_image {β : Type*} [DecidableEq β] {f : α
 -> β} : (s.image f).powerset = s.powerset.image (·.image f)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `Finset.image_injOn_powerset_of_injOn`：image_injOn_powerset_of_injOn {β :
 Type*} [DecidableEq β] {f : α -> β} (H : Set.InjOn f s) : Set.InjOn (α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem iterate_derivative_interpolate (hvs : Set.InjOn v s) {k : ℕ} (hk : k < #s) :
    derivative^[k] (interpolate s v r) =
      k.factorial * ∑ i ∈ s, C (r i / ∏ j ∈ s.erase i, (v i - v j)) *
        ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (X - C (v a)) := by
  classical
  simp_rw [interpolate_eq_sum, iterate_derivative_sum, iterate_derivative_C_mul, mul_sum s,
    ← mul_assoc, mul_comm (k.factorial : F[X]), mul_assoc]
  congr! 2 with i hi
  have hvs' := hvs.mono (coe_subset.mpr (erase_subset i s))
  calc
    derivative^[k] (∏ j ∈ s.erase i, (X - C (v j))) =
    derivative^[k] (∏ vj ∈ (s.erase i).image v, (X - C vj)) := by rw [Finset.prod_image hvs']
    _ = k.factorial * ∑ t ∈ ((s.erase i).image v).powersetCard (#s - (k + 1)),
          ∏ va ∈ t, (X - C va) := by
        grind [iterate_derivative_prod_X_sub_C]
    _ = k.factorial * ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (X - C (v a)) := by
        rw [powersetCard_eq_filter, powerset_image, eq_comm]
        congrm k.factorial * ?_
        refine sum_nbij (·.image v) (fun a ha ↦ ?hi) ?i_inj (fun t ht ↦ ?i_surj) fun a ha ↦ ?h
        case hi => grind [card_image_of_injOn, hvs'.mono]
        case i_inj => exact (image_injOn_powerset_of_injOn hvs').mono (by grind)
        case i_surj => grind [card_image_of_injOn, hvs'.mono]
        case h => exact eq_comm.mp <| prod_image <| by grind [hvs'.mono]
/-
**Lagrange.eval_iterate_derivative_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_iterate_derivative_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (h
P : P.degree < #s) {k : Nat} (hk : k < #s) (x : F) : (derivative^[k] P).eval x =
 k.factorial * ∑ i in s, (P.eval (v i) / ∏ j in s.erase i, (v i - v j)) * ∑ t in
 (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (x - v a)
参数：hvs : Set.InjOn v s；hP : P.degree < #s；hk : k < #s；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eq_interpolate`：eq_interpolate {f : F[X]} (hvs : Set.InjOn v s)
 (degree_f_lt : f.degree < #s) : f = interpolate s v fun i => f.eval (v i)
· 使用定理 `Lagrange.iterate_derivative_interpolate`：iterate_derivative_interpolate 
(hvs : Set.InjOn v s) {k : Nat} (hk : k < #s) : derivative^[k] (interpolate s v 
r) = k.factorial * ∑ i in s, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_iterate_derivative_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s)
    {k : ℕ} (hk : k < #s) (x : F) :
    (derivative^[k] P).eval x =
      k.factorial * ∑ i ∈ s, (P.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) *
        ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (x - v a) := by
  nth_rewrite 1 [eq_interpolate hvs hP, iterate_derivative_interpolate _ hvs hk]
  simp [eval_finsetSum, eval_prod]

@[deprecated eq_interpolate (since := "2026-01-14")]
/-
**Lagrange.interpolate_poly_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：interpolate_poly_eq_self (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.
degree < s.card) : interpolate s v (fun i => P.eval (v i)) = P
参数：hvs : Set.InjOn v s；hP : P.degree < s.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.eq_interpolate`：eq_interpolate {f : F[X]} (hvs : Set.InjOn v s)
 (degree_f_lt : f.degree < #s) : f = interpolate s v fun i => f.eval (v i)
-/
theorem interpolate_poly_eq_self
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < s.card) :
    interpolate s v (fun i => P.eval (v i)) = P := (eq_interpolate hvs hP).symm
/-
**Lagrange.coeff_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：coeff_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s)
 : P.coeff (#s - 1) = ∑ i in s, (P.eval (v i)) / ∏ j in s.erase i, (v i - v j)
参数：hvs : Set.InjOn v s；hP : P.degree < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eq_interpolate`：eq_interpolate {f : F[X]} (hvs : Set.InjOn v s)
 (degree_f_lt : f.degree < #s) : f = interpolate s v fun i => f.eval (v i)
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.natDegree_basis`：natDegree_basis (hvs : Set.InjOn v s) (hi : i 
in s) : (Lagrange.basis s v i).natDegree = #s - 1
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Lagrange.leadingCoeff_basis`：leadingCoeff_basis (hvs : Set.InjOn v s) (h
i : i in s) : (Lagrange.basis s v i).leadingCoeff = (∏ j in s.erase i, ((v i) - 
(v j)))⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_subst`：eq_div_of_subst {M : Type*} [D
iv M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n) (hd : l_d = d) : l 
= n / d
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'`：cons_eq_div_of_eq_di
v' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.
eval / t_d.eval) : ((-n, e) ::ᵣ t).eval …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
（共 36 条，此处仅展示前 30 条）
-/
theorem coeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s) :
    P.coeff (#s - 1) = ∑ i ∈ s, (P.eval (v i)) / ∏ j ∈ s.erase i, (v i - v j) := by
  nth_rewrite 1 [eq_interpolate hvs hP, interpolate_apply, finsetSum_coeff]
  congr! with i hi
  rw [coeff_C_mul, ← natDegree_basis hvs hi, ← leadingCoeff, leadingCoeff_basis hvs hi]
  field_simp
/-
**Lagrange.leadingCoeff_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：leadingCoeff_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (hP : #s = P.
degree + 1) : P.leadingCoeff = ∑ i in s, (P.eval (v i)) / ∏ j in s.erase i, (v i
 - v j)
参数：hvs : Set.InjOn v s；hP : #s = P.degree + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Lagrange.coeff_eq_sum`：coeff_eq_sum (hvs : Set.InjOn v s) {P : Polynomia
l F} (hP : P.degree < #s) : P.coeff (#s - 1) = ∑ i in s, (P.eval (v i)) / ∏ j in
 s.erase i,…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem leadingCoeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : #s = P.degree + 1) :
    P.leadingCoeff = ∑ i ∈ s, (P.eval (v i)) / ∏ j ∈ s.erase i, (v i - v j) := by
  lift P.degree to ℕ using (by contrapose! hP; simp [hP]) with deg hdeg
  rw [← WithBot.coe_one, ← WithBot.coe_add] at hP
  replace hP : #s = deg + 1 := WithBot.coe_eq_coe.mp hP
  have hdegree : P.degree = ↑(#s - 1) := hdeg.symm.trans (WithBot.coe_eq_coe.mpr (by grind))
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some hdegree]
  exact coeff_eq_sum hvs (by rw [hdegree]; norm_cast; lia)
/-
**Lagrange._root_.Polynomial.exists_eval_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Lagra
nge`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Polynomial.exists_eval_eq_iff {ι : Type*} [Finite ι] (x y : ι → F) :
    (∃ q : F[X], ∀ i, q.eval (x i) = y i) ↔ ∀ i j, x i = x j → y i = y j := by
  refine ⟨fun ⟨q, hq⟩ i j hij ↦ by rw [← hq, ← hq, hij], fun hwd ↦ ?_⟩
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hinj : Set.InjOn (fun d : F ↦ d) (Finset.univ.image x) := Function.injective_id.injOn
  set v : F → F := fun z ↦ if h : ∃ i, x i = z then y h.choose else 0 with v_def
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F ↦ d) v, fun i ↦ ?_⟩
  rw [Lagrange.eval_interpolate_at_node _ hinj (by simp), v_def]
  simp only
  split_ifs with h
  · exact hwd _ _ h.choose_spec
  · aesop

end Interpolate

section Nodal

variable {R : Type*} [CommRing R] {ι : Type*}
variable {s : Finset ι} {v : ι → R}

open Finset Polynomial

/-- `nodal s v` is the unique monic polynomial whose roots are the nodes defined by `v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
/-
**Lagrange.nodal** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：nodal (s : Finset ι) (v : ι -> R) : R[X]
参数：s : Finset ι；v : ι -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nodal s v` is the unique monic polynomial whose roots are the nodes defined by 
`v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
def nodal (s : Finset ι) (v : ι → R) : R[X] :=
  ∏ i ∈ s, (X - C (v i))
/-
**Lagrange.nodal_eq** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_eq (s : Finset ι) (v : ι -> R) : nodal s v = ∏ i in s, (X - C (v i))
参数：s : Finset ι；v : ι -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodal_eq (s : Finset ι) (v : ι → R) : nodal s v = ∏ i ∈ s, (X - C (v i)) :=
  rfl

@[simp]
/-
**Lagrange.nodal_empty** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_empty : nodal ∅ v = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodal_empty : nodal ∅ v = 1 := by
  rfl

@[simp]
/-
**Lagrange.natDegree_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_prod_of_monic`：natDegree_prod_of_monic (h : forall 
i in s, (f i).Monic) : (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s := by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
/-
**Lagrange.nodal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_ne_zero [Nontrivial R] : nodal s v != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.natDegree_nodal`：natDegree_nodal [Nontrivial R] : (nodal s v).n
atDegree = #s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
-/
theorem nodal_ne_zero [Nontrivial R] : nodal s v ≠ 0 := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]
/-
**Lagrange.degree_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：degree_nodal [Nontrivial R] : (nodal s v).degree = #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Lagrange.nodal_ne_zero`：nodal_ne_zero [Nontrivial R] : nodal s v != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lagrange.natDegree_nodal`：natDegree_nodal [Nontrivial R] : (nodal s v).n
atDegree = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_nodal [Nontrivial R] : (nodal s v).degree = #s := by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]
/-
**Lagrange.nodal_monic** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_monic : (nodal s v).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem nodal_monic : (nodal s v).Monic :=
  monic_prod_of_monic s (fun i ↦ X - C (v i)) fun i _ ↦ monic_X_sub_C (v i)
/-
**Lagrange.eval_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_nodal {x : R} : (nodal s v).eval x = ∏ i in s, (x - v i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_nodal {x : R} : (nodal s v).eval x = ∏ i ∈ s, (x - v i) := by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]
/-
**Lagrange.eval_nodal_at_node** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_nodal_at_node {i : ι} (hi : i in s) : eval (v i) (nodal s v) = 0
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eval_nodal`：eval_nodal {x : R} : (nodal s v).eval x = ∏ i in s,
 (x - v i)
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem eval_nodal_at_node {i : ι} (hi : i ∈ s) : eval (v i) (nodal s v) = 0 := by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))
/-
**Lagrange.eval_nodal_not_at_node** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_nodal_not_at_node [Nontrivial R] [NoZeroDivisors R] {x : R} (hx : for
all i in s, x != v i) : eval x (nodal s v) != 0
参数：hx : forall i in s, x != v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem eval_nodal_not_at_node [Nontrivial R] [NoZeroDivisors R] {x : R}
    (hx : ∀ i ∈ s, x ≠ v i) : eval x (nodal s v) ≠ 0 := by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx
/-
**Lagrange.nodal_eq_mul_nodal_erase** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_eq_mul_nodal_erase [DecidableEq ι] {i : ι} (hi : i in s) : nodal s v
 = (X - C (v i)) * nodal (s.erase i) v
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nodal_eq_mul_nodal_erase [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    nodal s v = (X - C (v i)) * nodal (s.erase i) v := by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]
/-
**Lagrange.X_sub_C_dvd_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：X_sub_C_dvd_nodal (v : ι -> R) {i : ι} (hi : i in s) : X - C (v i) ∣ nodal
 s v
参数：v : ι -> R；hi : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Lagrange.nodal_eq_mul_nodal_erase`：nodal_eq_mul_nodal_erase [DecidableEq
 ι] {i : ι} (hi : i in s) : nodal s v = (X - C (v i)) * nodal (s.erase i) v
-/
theorem X_sub_C_dvd_nodal (v : ι → R) {i : ι} (hi : i ∈ s) : X - C (v i) ∣ nodal s v := by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩
/-
**Lagrange.nodal_insert_eq_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_insert_eq_nodal [DecidableEq ι] {i : ι} (hi : i ∉ s) : nodal (insert
 i s) v = (X - C (v i)) * nodal s v
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nodal_insert_eq_nodal [DecidableEq ι] {i : ι} (hi : i ∉ s) :
    nodal (insert i s) v = (X - C (v i)) * nodal s v := by
  simp_rw [nodal, prod_insert hi]
/-
**Lagrange.derivative_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：derivative_nodal [DecidableEq ι] : derivative (nodal s v) = ∑ i in s, noda
l (s.erase i) v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.nodal_empty`：nodal_empty : nodal ∅ v = 1
· 使用定理 `Polynomial.derivative_one`：derivative_one : derivative (1 : R[X]) = 0
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Lagrange.nodal_insert_eq_nodal`：nodal_insert_eq_nodal [DecidableEq ι] {i
 : ι} (hi : i ∉ s) : nodal (insert i s) v = (X - C (v i)) * nodal s v
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.erase_insert_of_ne`：erase_insert_of_ne {a b : α} {s : Finset α} (
h : a != b) : (insert a s).erase b = insert a (s.erase b)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
-/
theorem derivative_nodal [DecidableEq ι] :
    derivative (nodal s v) = ∑ i ∈ s, nodal (s.erase i) v := by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm,
      nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]
/-
**Lagrange.eval_nodal_derivative_eval_node_eq** 是 Mathlib 中的一个定理，位于命名空间 `Lagrang
e`。
形式化陈述：eval_nodal_derivative_eval_node_eq [DecidableEq ι] {i : ι} (hi : i in s) :
 eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v)
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.derivative_nodal`：derivative_nodal [DecidableEq ι] : derivative
 (nodal s v) = ∑ i in s, nodal (s.erase i) v
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Lagrange.eval_nodal_at_node`：eval_nodal_at_node {i : ι} (hi : i in s) : 
eval (v i) (nodal s v) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eval_nodal_derivative_eval_node_eq [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v) := by
  rw [derivative_nodal, eval_finsetSum, ← add_sum_erase _ _ hi, add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

/-- The vanishing polynomial on a multiplicative subgroup is of the form X ^ n - 1. -/
/-
**Lagrange.nodal_subgroup_eq_X_pow_card_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Lagra
nge`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] (G : Subgroup Rˣ) [inst_
2 : Fintype ↥G],   Lagrange.nodal (↑G).toFinset Units.val = Polynomial.X ^ Finty
pe.card ↥G - 1
参数：G : Subgroup Rˣ；↑G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Polynomial.degree_pow`：degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : 
degree (p ^ n) = n • degree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Polynomial.eq_of_degree_le_of_eval_index_eq`：eq_of_degree_le_of_eval_ind
ex_eq (hvs : Set.InjOn v s) (h_deg_le : f.degree <= #s) (h_deg_eq : f.degree = g
.degree) (hlc : f.leadingCoeff = …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Lagrange.degree_nodal`：degree_nodal [Nontrivial R] : (nodal s v).degree 
= #s
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Lagrange.nodal_monic`：nodal_monic : (nodal s v).Monic
· 使用定理 `Polynomial.leadingCoeff_sub_of_degree_lt`：leadingCoeff_sub_of_degree_lt 
(h : Polynomial.degree q < Polynomial.degree p) : (p - q).leadingCoeff = p.leadi
ngCoeff
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Lagrange.eval_nodal_at_node`：eval_nodal_at_node {i : ι} (hi : i in s) : 
eval (v i) (nodal s v) = 0
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The vanishing polynomial on a multiplicative subgroup is of the form X ^ n - 1.
-/
@[simp] theorem nodal_subgroup_eq_X_pow_card_sub_one [IsDomain R]
    (G : Subgroup Rˣ) [Fintype G] :
    nodal (G : Set Rˣ).toFinset ((↑) : Rˣ → R) = X ^ (Fintype.card G) - 1 := by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ → R)) (G : Set Rˣ).toFinset
  · exact Units.val_injective.injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intro i hi
    rw [eval_nodal_at_node hi]
    replace hi : i ∈ G := by simpa using hi
    obtain ⟨g, rfl⟩ : ∃ g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]

end Nodal

section NodalWeight

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i : ι}

open Finset

/-- This defines the nodal weight for a given set of node indexes and node mapping function `v`. -/
/-
**Lagrange.nodalWeight** 是 Mathlib 中的一个定义，位于命名空间 `Lagrange`。
形式化陈述：nodalWeight (s : Finset ι) (v : ι -> F) (i : ι)
参数：s : Finset ι；v : ι -> F；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This defines the nodal weight for a given set of node indexes and node mapping f
unction `v`.
-/
def nodalWeight (s : Finset ι) (v : ι → F) (i : ι) :=
  ∏ j ∈ s.erase i, (v i - v j)⁻¹
/-
**Lagrange.nodalWeight_eq_eval_nodal_erase_inv** 是 Mathlib 中的一个定理，位于命名空间 `Lagran
ge`。
形式化陈述：nodalWeight_eq_eval_nodal_erase_inv : nodalWeight s v i = (eval (v i) (nod
al (s.erase i) v))⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eval_nodal`：eval_nodal {x : R} : (nodal s v).eval x = ∏ i in s,
 (x - v i)
· 使用定理 `Lagrange.nodalWeight.eq_1`：∀ {F : Type u_1} [inst : Field F] {ι : Type u
_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v : ι → F) (i : ι),   Lagrange.noda
lWeight s v i =…
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
-/
theorem nodalWeight_eq_eval_nodal_erase_inv :
    nodalWeight s v i = (eval (v i) (nodal (s.erase i) v))⁻¹ := by
  rw [eval_nodal, nodalWeight, prod_inv_distrib]
/-
**Lagrange.nodal_erase_eq_nodal_div** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodal_erase_eq_nodal_div (hi : i in s) : nodal (s.erase i) v = nodal s v /
 (X - C (v i))
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.nodal_eq_mul_nodal_erase`：nodal_eq_mul_nodal_erase [DecidableEq
 ι] {i : ι} (hi : i in s) : nodal s v = (X - C (v i)) * nodal (s.erase i) v
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem nodal_erase_eq_nodal_div (hi : i ∈ s) :
    nodal (s.erase i) v = nodal s v / (X - C (v i)) := by
  rw [nodal_eq_mul_nodal_erase hi, mul_div_cancel_left₀]
  exact X_sub_C_ne_zero _
/-
**Lagrange.nodalWeight_eq_eval_derivative_nodal** 是 Mathlib 中的一个定理，位于命名空间 `Lagra
nge`。
形式化陈述：nodalWeight_eq_eval_derivative_nodal (hi : i in s) : nodalWeight s v i = (
eval (v i) (Polynomial.derivative (nodal s v)))⁻¹
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.eval_nodal_derivative_eval_node_eq`：eval_nodal_derivative_eval_
node_eq [DecidableEq ι] {i : ι} (hi : i in s) : eval (v i) (derivative (nodal s 
v)) = eval (v i) (nodal (s.erase …
· 使用定理 `Lagrange.nodalWeight_eq_eval_nodal_erase_inv`：nodalWeight_eq_eval_nodal_
erase_inv : nodalWeight s v i = (eval (v i) (nodal (s.erase i) v))⁻¹
-/
theorem nodalWeight_eq_eval_derivative_nodal (hi : i ∈ s) :
    nodalWeight s v i = (eval (v i) (Polynomial.derivative (nodal s v)))⁻¹ := by
  rw [eval_nodal_derivative_eval_node_eq hi, nodalWeight_eq_eval_nodal_erase_inv]
/-
**Lagrange.nodalWeight_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：nodalWeight_ne_zero (hvs : Set.InjOn v s) (hi : i in s) : nodalWeight s v 
i != 0
参数：hvs : Set.InjOn v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.nodalWeight.eq_1`：∀ {F : Type u_1} [inst : Field F] {ι : Type u
_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v : ι → F) (i : ι),   Lagrange.noda
lWeight s v i =…
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem nodalWeight_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : nodalWeight s v i ≠ 0 := by
  rw [nodalWeight, prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))

end NodalWeight

section LagrangeBarycentric

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} (r : ι → F) {i : ι} {x : F}

open Finset

/-
**Lagrange.basis_eq_prod_sub_inv_mul_nodal_div** 是 Mathlib 中的一个定理，位于命名空间 `Lagran
ge`。
形式化陈述：basis_eq_prod_sub_inv_mul_nodal_div (hi : i in s) : Lagrange.basis s v i =
 C (nodalWeight s v i) * (nodal s v / (X - C (v i)))
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.nodal_erase_eq_nodal_div`：nodal_erase_eq_nodal_div (hi : i in s
) : nodal (s.erase i) v = nodal s v / (X - C (v i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_eq_prod_sub_inv_mul_nodal_div (hi : i ∈ s) :
    Lagrange.basis s v i = C (nodalWeight s v i) * (nodal s v / (X - C (v i))) := by
  simp_rw [Lagrange.basis, basisDivisor, nodalWeight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]
/-
**Lagrange.eval_basis_not_at_node** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_basis_not_at_node (hi : i in s) (hxi : x != v i) : eval x (Lagrange.b
asis s v i) = eval x (nodal s v) * (nodalWeight s v i * (x - v i)⁻¹)
参数：hi : i in s；hxi : x != v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`：basis_eq_prod_sub_inv_mul_
nodal_div (hi : i in s) : Lagrange.basis s v i = C (nodalWeight s v i) * (nodal 
s v / (X - C (v i)))
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.nodal_erase_eq_nodal_div`：nodal_erase_eq_nodal_div (hi : i in s
) : nodal (s.erase i) v = nodal s v / (X - C (v i))
· 使用定理 `Lagrange.eval_nodal`：eval_nodal {x : R} : (nodal s v).eval x = ∏ i in s,
 (x - v i)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem eval_basis_not_at_node (hi : i ∈ s) (hxi : x ≠ v i) :
    eval x (Lagrange.basis s v i) = eval x (nodal s v) * (nodalWeight s v i * (x - v i)⁻¹) := by
  rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hi, eval_mul, eval_C, ←
    nodal_erase_eq_nodal_div hi, eval_nodal, eval_nodal, mul_assoc, ← mul_prod_erase _ _ hi, ←
    mul_assoc (x - v i)⁻¹, inv_mul_cancel₀ (sub_ne_zero_of_ne hxi), one_mul]
/-
**Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C** 是 Mathlib 中的一个定理，位
于命名空间 `Lagrange`。
形式化陈述：interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C : interpolate s v r = ∑ i
 in s, C (nodalWeight s v i) * (nodal s v / (X - C (v i))) * C (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`：basis_eq_prod_sub_inv_mul_
nodal_div (hi : i in s) : Lagrange.basis s v i = C (nodalWeight s v i) * (nodal 
s v / (X - C (v i)))
-/
theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C :
    interpolate s v r = ∑ i ∈ s, C (nodalWeight s v i) * (nodal s v / (X - C (v i))) * C (r i) :=
  sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]

/-- This is the first barycentric form of the Lagrange interpolant. -/
/-
**Lagrange.eval_interpolate_not_at_node** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_interpolate_not_at_node (hx : forall i in s, x != v i) : eval x (inte
rpolate s v r) = eval x (nodal s v) * ∑ i in s, nodalWeight s v i * (x - v i)⁻¹ 
* r i
参数：hx : forall i in s, x != v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lagrange.interpolate_apply`：∀ {F : Type u_1} [inst : Field F] {ι : Type 
u_2} [inst_1 : DecidableEq ι] (s : Finset ι) (v r : ι → F),   (Lagrange.interpol
ate s v) r = ∑ i…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Lagrange.eval_basis_not_at_node`：eval_basis_not_at_node (hi : i in s) (h
xi : x != v i) : eval x (Lagrange.basis s v i) = eval x (nodal s v) * (nodalWeig
ht s v i * (x - v i)⁻…

--- 原说明 ---
This is the first barycentric form of the Lagrange interpolant.
-/
theorem eval_interpolate_not_at_node (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      eval x (nodal s v) * ∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ * r i := by
  simp_rw [interpolate_apply, mul_sum, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, mul_comm, eval_basis_not_at_node hi (hx _ hi)]
/-
**Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lagran
ge`。
形式化陈述：sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : forall i i
n s, x != v i) (hs : s.Nonempty) : (∑ i in s, nodalWeight s v i * (x - v i)⁻¹) !
= 0
参数：hvs : Set.InjOn v s；hx : forall i in s, x != v i；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_ne_zero_of_mul_eq_one`：right_ne_zero_of_mul_eq_one (h : a * b = 1)
 : b != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lagrange.interpolate_one`：interpolate_one (hvs : Set.InjOn v s) (hs : s.
Nonempty) : interpolate s v 1 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lagrange.eval_interpolate_not_at_node`：eval_interpolate_not_at_node (hx 
: forall i in s, x != v i) : eval x (interpolate s v r) = eval x (nodal s v) * ∑
 i in s, nodalWeight s v i …
-/
theorem sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : ∀ i ∈ s, x ≠ v i)
    (hs : s.Nonempty) : (∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹) ≠ 0 :=
  @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ <| by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm

/-- This is the second barycentric form of the Lagrange interpolant. -/
/-
**Lagrange.eval_interpolate_not_at_node'** 是 Mathlib 中的一个定理，位于命名空间 `Lagrange`。
形式化陈述：eval_interpolate_not_at_node' (hvs : Set.InjOn v s) (hs : s.Nonempty) (hx 
: forall i in s, x != v i) : eval x (interpolate s v r) = (∑ i in s, nodalWeight
 s v i * (x - v i)⁻¹ * r i) / ∑ i in s, nodalWeight s v i * (x - v i)⁻¹
参数：hvs : Set.InjOn v s；hs : s.Nonempty；hx : forall i in s, x != v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Lagrange.interpolate_one`：interpolate_one (hvs : Set.InjOn v s) (hs : s.
Nonempty) : interpolate s v 1 = 1
· 使用定理 `Lagrange.eval_interpolate_not_at_node`：eval_interpolate_not_at_node (hx 
: forall i in s, x != v i) : eval x (interpolate s v r) = eval x (nodal s v) * ∑
 i in s, nodalWeight s v i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `Lagrange.eval_nodal_not_at_node`：eval_nodal_not_at_node [Nontrivial R] [
NoZeroDivisors R] {x : R} (hx : forall i in s, x != v i) : eval x (nodal s v) !=
 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is the second barycentric form of the Lagrange interpolant.
-/
theorem eval_interpolate_not_at_node' (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      (∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ * r i) /
        ∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ := by
  rw [← div_one (eval x (interpolate s v r)), ← @eval_one _ _ x, ← interpolate_one hvs hs,
    eval_interpolate_not_at_node r hx, eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]

end LagrangeBarycentric

end Lagrange

