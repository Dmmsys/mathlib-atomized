/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in polynomial rings
-/

public section

noncomputable section

open Polynomial

open Finset

universe u v w

namespace Polynomial

variable {R : Type*} [CommRing R] {a : R}

/-
**Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} 
: P in Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_pair`：mem_span_pair {x y z : α} : z in span ({x, y} : Set
 α) ↔ exists a b, a * x + b * y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Polynomial.X_sub_C_dvd_sub_C_eval`：X_sub_C_dvd_sub_C_eval : X - C a ∣ p 
- C (p.eval a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_add_of_sub_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 a - b = c → a = b + c
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
-/
theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P ∈ Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩
/-
**Polynomial.ker_evalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C 
x}
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]

@[simp]
/-
**Polynomial.ker_modByMonicHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ker_modByMonicHom {q : R[X]} (hq : q.Monic) : LinearMap.ker (Polynomial.mo
dByMonicHom q) = (Ideal.span {q}).restrictScalars R
参数：hq : q.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.mem_ker_modByMonic`：mem_ker_modByMonic (hq : q.Monic) {p : R[
X]} : p in LinearMap.ker (modByMonicHom q) ↔ q ∣ p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
-/
theorem ker_modByMonicHom {q : R[X]} (hq : q.Monic) :
    LinearMap.ker (Polynomial.modByMonicHom q) = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

@[simp]
/-
**Polynomial.ker_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：ker_constantCoeff : RingHom.ker constantCoeff = .span {(X : R[X])}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.constantCoeff_apply`：∀ {R : Type u} [inst : Semiring R] (p : 
Polynomial R), Polynomial.constantCoeff p = p.coeff 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_constantCoeff : RingHom.ker constantCoeff = .span {(X : R[X])} := by
  refine le_antisymm (fun p hp ↦ ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, constantCoeff_apply, ← Polynomial.X_dvd_iff] at hp
  rwa [Ideal.mem_span_singleton]

end Polynomial

namespace Algebra

variable {R S : Type*}

/-
**Algebra.mem_ideal_map_adjoin** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：mem_ideal_map_adjoin [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (
I : Ideal R) {y : R[x]} : y in I.map (algebraMap R (R[x])) ↔ exists p : R[X], (f
orall i, p.coeff i in I) ∧ Polynomial.aeval x p = y
参数：x : S；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.aeval_zero`：aeval_zero : aeval x (0 : R[X]) = 0
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.adjoin_eq_exists_aeval`：adjoin_eq_exists_aeval (a : R[x]) : exis
ts p : R[X], aeval x p = a
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
（共 48 条，此处仅展示前 30 条）
-/
lemma mem_ideal_map_adjoin [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (I : Ideal R)
    {y : R[x]} :
    y ∈ I.map (algebraMap R (R[x])) ↔
      ∃ p : R[X], (∀ i, p.coeff i ∈ I) ∧ Polynomial.aeval x p = y := by
  constructor
  · intro H
    induction H using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨C a, fun i ↦ by rw [coeff_C]; aesop, aeval_C _ _⟩
    | zero => exact ⟨0, by simp, aeval_zero _⟩
    | add a b ha hb ha' hb' =>
      obtain ⟨a, ha, ha'⟩ := ha'
      obtain ⟨b, hb, hb'⟩ := hb'
      exact ⟨a + b, fun i ↦ by simpa using add_mem (ha i) (hb i), by simp [ha', hb']⟩
    | smul a b hb hb' =>
      obtain ⟨b', hb, hb'⟩ := hb'
      have ⟨p, hp⟩ := adjoin_eq_exists_aeval R x a
      refine ⟨p * b', fun i ↦ ?_, by simp [hp, hb']⟩
      rw [coeff_mul]
      exact sum_mem fun i hi ↦ Ideal.mul_mem_left _ _ (hb _)
  · rintro ⟨p, hp, hp'⟩
    have : y = ∑ i ∈ p.support, p.coeff i • ⟨_, (X ^ i).aeval_mem_adjoin_singleton _ x⟩ := by
      trans ∑ i ∈ p.support, ⟨_, (C (p.coeff i) * X ^ i).aeval_mem_adjoin_singleton _ x⟩
      · ext1
        simp only [AddSubmonoidClass.coe_finsetSum, ← map_sum, ← hp', ← as_sum_support_C_mul_X_pow]
      · congr with i
        simp [Algebra.smul_def]
    simp_rw [this, Algebra.smul_def]
    exact sum_mem fun i _ ↦ Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp i))
/-
**Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top** 是 Math
lib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R]
 [CommRing S] [Algebra R S] (x : S) (I : Ideal R) (hI : I != ⊤) [Invertible x] (
h : I.map (algebraMap R (R[x])) ⊔ .span {⟨x, subset_adjoin rfl⟩} = ⊤) : exists p
 : R[X], p.leadingCoeff - 1 in I ∧ p.aeval ⅟x = 0
参数：x : S；I : Ideal R；hI : I != ⊤；h : I.map (algebraMap R (R[x])) ⊔ .span {⟨x, su
bset_adjoin rfl⟩} = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.add_eq_one_iff`：add_eq_one_iff : I + J = 1 ↔ exists i in I, exists
 j in J, i + j = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.add_eq_sup`：add_eq_sup {I J : Ideal R} : I + J = I ⊔ J
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.mem_ideal_map_adjoin`：mem_ideal_map_adjoin [CommSemiring R] [Sem
iring S] [Algebra R S] (x : S) (I : Ideal R) {y : R[x]} : y in I.map (algebraMap
 R (R[x])) ↔ exist…
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Algebra.adjoin_eq_exists_aeval`：adjoin_eq_exists_aeval (a : R[x]) : exis
ts p : R[X], aeval x p = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.reverse_leadingCoeff`：reverse_leadingCoeff (f : R[X]) : f.rev
erse.leadingCoeff = f.trailingCoeff
· 使用定理 `Polynomial.trailingCoeff_eq_coeff_zero`：trailingCoeff_eq_coeff_zero (h :
 coeff p 0 != 0) : trailingCoeff p = coeff p 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.eval₂_reverse_eq_zero_iff`：eval₂_reverse_eq_zero_iff (i : R -
>+* S) (x : S) [Invertible x] (f : R[X]) : eval₂ i (⅟x) (reverse f) = 0 ↔ eval₂ 
i x f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
（共 38 条，此处仅展示前 30 条）
-/
lemma exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (I : Ideal R) (hI : I ≠ ⊤) [Invertible x]
    (h : I.map (algebraMap R (R[x])) ⊔ .span {⟨x, subset_adjoin rfl⟩} = ⊤) :
    ∃ p : R[X], p.leadingCoeff - 1 ∈ I ∧ p.aeval ⅟x = 0 := by
  rw [← Ideal.one_eq_top, ← Ideal.add_eq_sup, Ideal.add_eq_one_iff] at h
  have ⟨y, hy, z, hz, eq⟩ := h
  have ⟨p, hp⟩ := (mem_ideal_map_adjoin ..).mp hy
  have ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have ⟨q, hq⟩ := adjoin_eq_exists_aeval R x w
  use (1 - p - X * q).reverse
  have : (1 - p - X * q).coeff 0 - 1 ∈ I := by simpa using hp.1 0
  apply_fun (·.1) at eq hw
  dsimp at eq
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero]
  · exact ⟨this, (eval₂_reverse_eq_zero_iff ..).mpr <| by simp [← aeval_def, hp.2, hq, ← eq, hw]⟩
  · exact fun h ↦ hI <| by simpa [h, Ideal.eq_top_iff_one]

end Algebra

