/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of Dedekind domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a
  fixed maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a prime of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

* `Ideal.card_inertia_eq_ramificationIdxIn`:
  The cardinality of the inertia group is equal to the ramification index.

## References

* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

@[expose] public section

open Algebra Module
open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from the theorem
  `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`. -/
/-
**Ideal.ramificationIdxIn** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A) (B : Type*) [Comm
Ring B] [Algebra A B] : Nat
参数：p : Ideal A；B : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L / K` is a Galois extension, it can be seen from the theorem
  `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` o
ver a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationI
dxIn`.
-/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.ramificationIdx A
  else 0

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`. -/
/-
**Ideal.inertiaDegIn** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A) (B : Type*) [CommRing 
B] [Algebra A B] : Nat
参数：p : Ideal A；B : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L / K` is a Galois extension, it can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg`
 over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`
.
-/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.inertiaDeg A else 0

section MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction G (primesOver p B) where
  smul σ Q := primesOver.mk p (σ • Q.1)
  one_smul Q := Subtype.ext (one_smul G Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

@[simp]
/-
**Ideal.coe_smul_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_smul_primesOver (σ : G) (P : primesOver p B) : (σ • P).1 = σ • P.1
参数：σ : G；P : primesOver p B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_primesOver (σ : G) (P : primesOver p B) : (σ • P).1 = σ • P.1 :=
  rfl

@[simp]
/-
**Ideal.coe_smul_primesOver_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_smul_primesOver_mk (σ : G) (P : Ideal B) [P.IsPrime] [P.LiesOver p] : 
(σ • primesOver.mk p P).1 = σ • P
参数：σ : G；P : Ideal B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_primesOver_mk (σ : G) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    (σ • primesOver.mk p P).1 = σ • P :=
  rfl

variable (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MulAction Gal(L/K) (primesOver p B) where
  smul σ Q := primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = Q.1
    simpa only [map_one] using! map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = map _ (map _ Q.1)
    rw [map_mul]
    exact (Q.1.map_map ((galRestrict A K L B) τ).toRingHom ((galRestrict A K L B) σ).toRingHom).symm
/-
**Ideal.coe_smul_primesOver_eq_map_galRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`
。
形式化陈述：coe_smul_primesOver_eq_map_galRestrict (σ : Gal(L/K)) (P : primesOver p B)
 : (σ • P).1 = map (galRestrict A K L B σ) P
参数：σ : Gal(L/K)；P : primesOver p B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_primesOver_eq_map_galRestrict (σ : Gal(L/K)) (P : primesOver p B) :
    (σ • P).1 = map (galRestrict A K L B σ) P :=
  rfl
/-
**Ideal.coe_smul_primesOver_mk_eq_map_galRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al`。
形式化陈述：coe_smul_primesOver_mk_eq_map_galRestrict (σ : Gal(L/K)) (P : Ideal B) [P.
IsPrime] [P.LiesOver p] : (σ • primesOver.mk p P).1 = map (galRestrict A K L B σ
) P
参数：σ : Gal(L/K)；P : Ideal B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_primesOver_mk_eq_map_galRestrict (σ : Gal(L/K)) (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] : (σ • primesOver.mk p P).1 = map (galRestrict A K L B σ) P :=
  rfl

end MulAction

section RamificationInertia

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] [hQp : Q.IsPrime] [Q.LiesOver p]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include p in
/-- If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In other words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals lying over `p`. -/
/-
**Ideal.exists_smul_eq_of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_smul_eq_of_isGaloisGroup : exists σ : G, σ • P = Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.exists_smul_of_under_eq`：exists_smul_of_under_eq [Fi
nite G] [SMulCommClass G A B] (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime] 
(hPQ : P.under A = Q.under A) : e…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A

--- 原说明 ---
If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In ot
her words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals
 lying over `p`.
-/
theorem exists_smul_eq_of_isGaloisGroup : ∃ σ : G, σ • P = Q := by
  rcases IsInvariant.exists_smul_of_under_eq A B G P Q <|
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩
/-
**Ideal.isPretransitive_of_isGaloisGroup** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：isPretransitive_of_isGaloisGroup : MulAction.IsPretransitive G (primesOver
 p B) where exists_smul_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Ideal.exists_smul_eq_of_isGaloisGroup`：exists_smul_eq_of_isGaloisGroup :
 exists σ : G, σ • P = Q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
-/
instance isPretransitive_of_isGaloisGroup : MulAction.IsPretransitive G (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

include p G in
/-- All the `Ideal.ramificationIdx` over a fixed maximal ideal are the same. -/
/-
**Ideal.ramificationIdx_eq_of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_eq_of_isGaloisGroup : P.ramificationIdx A = Q.ramification
Idx A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_smul_eq_of_isGaloisGroup`：exists_smul_eq_of_isGaloisGroup :
 exists σ : G, σ • P = Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_smul`：ramificationIdx_smul {G : Type*} [Group G] [
MulSemiringAction G S] [SMulCommClass G R S] (g : G) : (g • q).ramificationIdx R
 = q.ramificatio…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…

--- 原说明 ---
All the `Ideal.ramificationIdx` over a fixed maximal ideal are the same.
-/
theorem ramificationIdx_eq_of_isGaloisGroup :
    P.ramificationIdx A = Q.ramificationIdx A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [ramificationIdx_smul]

include p G in
/-- All the `Ideal.inertiaDeg` over a fixed maximal ideal are the same. -/
/-
**Ideal.inertiaDeg_eq_of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_eq_of_isGaloisGroup : P.inertiaDeg A = Q.inertiaDeg A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_smul_eq_of_isGaloisGroup`：exists_smul_eq_of_isGaloisGroup :
 exists σ : G, σ • P = Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg_smul`：inertiaDeg_smul {G : Type*} [Group G] [MulSemirin
gAction G S] [SMulCommClass G R S] (g : G) : (g • q).inertiaDeg R = q.inertiaDeg
 R
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…

--- 原说明 ---
All the `Ideal.inertiaDeg` over a fixed maximal ideal are the same.
-/
theorem inertiaDeg_eq_of_isGaloisGroup :
    P.inertiaDeg A = Q.inertiaDeg A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [inertiaDeg_smul]

include p G in
/-- The `ramificationIdxIn` is equal to any ramification index over the same ideal. -/
/-
**Ideal.ramificationIdxIn_eq_ramificationIdx** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdxIn_eq_ramificationIdx : ramificationIdxIn p B = P.ramificat
ionIdx A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdxIn.eq_1`：∀ {A : Type u_1} [inst : CommRing A] (p : 
Ideal A) (B : Type u_2) [inst_1 : CommRing B] [inst_2 : Algebra A B],   p.ramifi
cationIdxIn B = if…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Ideal.ramificationIdx_eq_of_isGaloisGroup`：ramificationIdx_eq_of_isGaloi
sGroup : P.ramificationIdx A = Q.ramificationIdx A

--- 原说明 ---
The `ramificationIdxIn` is equal to any ramification index over the same ideal.
-/
theorem ramificationIdxIn_eq_ramificationIdx :
    ramificationIdxIn p B = P.ramificationIdx A := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn, dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in
/-
**Ideal.ramificationIdxIn_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdxIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Idea
l A} [p.IsPrime] : p.ramificationIdxIn B != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.ramificationIdx_pos`：ramificationIdx_pos [q.IsPrime] [Module.Finit
e R S] : 0 < q.ramificationIdx R
-/
theorem ramificationIdxIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    p.ramificationIdxIn B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact (P.1.ramificationIdx_pos A).ne'

include G in
/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
/-
**Ideal.inertiaDegIn_eq_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDegIn_eq_inertiaDeg : inertiaDegIn p B = P.inertiaDeg A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDegIn.eq_1`：∀ {A : Type u_1} [inst : CommRing A] (p : Ideal
 A) (B : Type u_2) [inst_1 : CommRing B] [inst_2 : Algebra A B],   p.inertiaDegI
n B = if h : …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Ideal.inertiaDeg_eq_of_isGaloisGroup`：inertiaDeg_eq_of_isGaloisGroup : P
.inertiaDeg A = Q.inertiaDeg A

--- 原说明 ---
The `inertiaDegIn` is equal to any ramification index over the same ideal.
-/
theorem inertiaDegIn_eq_inertiaDeg :
    inertiaDegIn p B = P.inertiaDeg A := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in
/-
**Ideal.inertiaDegIn_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDegIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} 
[p.IsPrime] : inertiaDegIn p B != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.inertiaDeg_pos`：inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S
] : 0 < q.inertiaDeg R
-/
theorem inertiaDegIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    inertiaDegIn p B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact (P.1.inertiaDeg_pos A).ne'

section tower

variable (C : Type*) [CommRing C] [Algebra A C] [Algebra B C]
  [Nonempty (P.primesOver C)] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]
  (GBC : Type*) [Group GBC] [Finite GBC] [MulSemiringAction GBC C] [IsGaloisGroup GBC B C]

include G GAC GBC in
/-
**Ideal.inertiaDegIn_mul_inertiaDegIn** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDegIn_mul_inertiaDegIn : p.inertiaDegIn B * P.inertiaDegIn C = p.in
ertiaDegIn C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDeg_tower`：inertiaDeg_tower [r.LiesOver q] : r.inertiaDeg R
 = q.inertiaDeg R * r.inertiaDeg S
-/
theorem inertiaDegIn_mul_inertiaDegIn :
    p.inertiaDegIn B * P.inertiaDegIn C = p.inertiaDegIn C := by
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P G, inertiaDegIn_eq_inertiaDeg p Q GAC,
    inertiaDegIn_eq_inertiaDeg P Q GBC, ← inertiaDeg_tower P Q]

variable {p} in
include G GAC GBC in
/-
**Ideal.ramificationIdxIn_mul_ramificationIdxIn** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：ramificationIdxIn_mul_ramificationIdxIn [Flat B C] : p.ramificationIdxIn B
 * P.ramificationIdxIn C = p.ramificationIdxIn C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdx_tower`：ramificationIdx_tower [r.LiesOver q] [Modul
e.Flat S T] : r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S
-/
theorem ramificationIdxIn_mul_ramificationIdxIn [Flat B C] :
    p.ramificationIdxIn B * P.ramificationIdxIn C = p.ramificationIdxIn C := by
  obtain ⟨⟨Q, _, hQ⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P G, ramificationIdxIn_eq_ramificationIdx p Q GAC,
    ramificationIdxIn_eq_ramificationIdx P Q GBC, ← ramificationIdx_tower P Q]

@[deprecated (since := "2026-06-18")] alias ramificationIdxIn_mul_ramificationIdxIn' :=
  ramificationIdxIn_mul_ramificationIdxIn

end tower

end RamificationInertia

section fundamental_identity

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Flat A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- The form of the **fundamental identity** in the case of Galois extension. -/
/-
**Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn** 是 Mathlib 中的一个
定理，位于命名空间 `Ideal`。
形式化陈述：ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn : (primesOver p B)
.ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.finite_primesOver`：finite_primesOver [QuasiFinite R 
S] (I : Ideal R) : (I.primesOver S).Finite
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Ideal.sum_ramification_inertia_eq_card`：sum_ramification_inertia_eq_card
 [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] [Fintype (p.pri
mesOver S)] {G : Type*} [Gro…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A

--- 原说明 ---
The form of the **fundamental identity** in the case of Galois extension.
-/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G := by
  have : Fintype (primesOver p B) := (QuasiFinite.finite_primesOver p).fintype
  rw [← smul_eq_mul, ← Set.fintypeCard_eq_ncard, ← Finset.card_univ, ← Finset.sum_const,
    ← sum_ramification_inertia_eq_card p B]
  apply Finset.sum_congr rfl
  intro P hp
  rw [ramificationIdxIn_eq_ramificationIdx p P G, inertiaDegIn_eq_inertiaDeg p P G]

end fundamental_identity

section tower

variable {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] [FaithfulSMul A B] {p : Ideal A} (P : Ideal B)
  [P.IsPrime] [P.LiesOver p] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B] (C : Type*) [CommRing C] [IsDomain C] [Algebra A C]
  [Algebra B C] [FaithfulSMul B C] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]

include G GAC in
open IsGaloisGroup MulAction in
/-
**Ideal.ncard_primesOver_mul_ncard_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ncard_primesOver_mul_ncard_primesOver : (p.primesOver B).ncard * (P.primes
Over C).ncard = (p.primesOver C).ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `Algebra.IsIntegral.tower_top`：Algebra.IsIntegral.tower_top [Algebra R S]
 [Algebra R T] [Algebra S T] [IsScalarTower R S T] [h : Algebra.IsIntegral R T] 
: Algebra.IsIntegr…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.restrictHom_smul_under`：restrictHom_smul_under [Finite G] 
[Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' 
B] [IsGaloisGroup G' A B] …
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsPrime.smul`：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [in
st_1 : Semiring R] [inst_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPri
me] (g :…
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Algebra.IsInvariant.exists_smul_of_under_eq`：exists_smul_of_under_eq [Fi
nite G] [SMulCommClass G A B] (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime] 
(hPQ : P.under A = Q.under A) : e…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.IsInvariant.orbit_eq_primesOver`：orbit_eq_primesOver [Finite G] 
[SMulCommClass G A B] (P : Ideal A) (Q : Ideal B) [hP : Q.LiesOver P] [hQ : Q.Is
Prime] : MulAction.orbit G Q …
· 使用定理 `MulAction.index_stabilizer`：∀ (G : Type u_1) {X : Type u_2} [inst : Grou
p G] [inst_1 : MulAction G X] (x : X),   (MulAction.stabilizer G x).index = (Mul
Action.orbit G x…
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.index_comap_of_surjective`：index_comap_of_surjective {f : G' ->
* G} (hf : Function.Surjective f) : (H.comap f).index = H.index
· 使用定理 `IsGaloisGroup.restrictHom_surjective`：restrictHom_surjective [Finite G] 
[Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' 
B] [IsGaloisGroup G' A B] …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
-/
theorem ncard_primesOver_mul_ncard_primesOver :
    (p.primesOver B).ncard * (P.primesOver C).ncard = (p.primesOver C).ncard := by
  have : Algebra.IsIntegral A C := isInvariant.isIntegral A C GAC
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let f := restrictHom GAC G A B C
  let H := (stabilizer G P).comap f
  have key (Q Q' : Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg : g • Q = Q') : g ∈ H := by
    simpa [← restrictHom_smul_under GAC G A, ← over_def _ P, H] using congr_arg (under B) hg
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (P.primesOver C))
  have : Q.LiesOver p := .trans Q P p
  have orbit_eq : orbit H Q = P.primesOver C := by
    ext Q'
    constructor
    · rintro ⟨g, rfl : g • Q = Q'⟩
      refine ⟨inferInstance, ?_⟩
      rw [liesOver_iff, H.smul_def, ← restrictHom_smul_under GAC G A B C, ← Q.over_def P]
      exact g.2.symm
    · rintro ⟨_, _⟩
      have : Q'.LiesOver p := .trans Q' P p
      obtain ⟨g, hg⟩ :=
        IsInvariant.exists_smul_of_under_eq A C GAC Q Q' ((Q.over_def p).symm.trans (Q'.over_def p))
      exact ⟨⟨g, key Q Q' g hg.symm⟩, by simpa [Subgroup.smul_def] using hg.symm⟩
  have stabilizer_eq : stabilizer H Q = (stabilizer GAC Q).subgroupOf H := by
    simp [Subgroup.ext_iff, Subgroup.mem_subgroupOf]
  rw [← IsInvariant.orbit_eq_primesOver A B G p P, ← index_stabilizer,
    ← orbit_eq, ← index_stabilizer, stabilizer_eq, ← Subgroup.relIndex,
    ← IsInvariant.orbit_eq_primesOver A C GAC p Q, ← index_stabilizer,
    ← (stabilizer G P).index_comap_of_surjective (restrictHom_surjective GAC G A B C),
    mul_comm, Subgroup.relIndex_mul_index]
  exact key Q Q

end tower

section inertia

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise

open Algebra

attribute [local instance] Ideal.Quotient.field in
/-
**Ideal.card_stabilizer_eq_card_inertia_mul_finrank** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：card_stabilizer_eq_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime] (P :
 Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] : Nat.card (M
ulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg R
参数：p : Ideal R；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsScalarTowerQuotientIdealResidueField`：∀ {R : Type u_1} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal 
A)   [inst_3 : I.IsPrime], IsSca…
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Ideal.IsFractionRing.normal`：normal : Normal K L
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用引理 `Ideal.IsFractionRing.finite_of_isInvariant`：finite_of_isInvariant [SMulC
ommClass G A B] [Algebra.IsSeparable K L] : Module.Finite K L
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Ideal.instNormalSubtypeMemSubgroupStabilizerInertia`：∀ {M : Type u_1} [i
nst : Group M] {R : Type u_4} [inst_1 : Ring R] (P : Ideal R) [inst_2 : MulSemir
ingAction M R],   (Ideal.inertia (↥(MulAc…
· 使用定理 `Ideal.inertiaDeg_eq`：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime
] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPr
ime.IsLie…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `Ideal.inertia_le_stabilizer`：inertia_le_stabilizer {R : Type*} [Ring R] 
(P : Ideal R) [MulSemiringAction M R] : inertia M P <= MulAction.stabilizer M P
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用引理 `AddSubgroup.subgroupOf_inertia`：subgroupOf_inertia (H : Subgroup G) : (I
.inertia G).subgroupOf H = I.inertia H
-/
theorem card_stabilizer_eq_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [inertiaDeg_eq p P, ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]
/-
**Ideal.ncard_primesOver_mul_card_inertia_mul_finrank** 是 Mathlib 中的一个引理，位于命名空间 
`Ideal`。
形式化陈述：ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime] (P
 : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] : (p.primes
Over S).ncard * Nat.card (P.inertia G) * P.inertiaDeg R = Nat.card G
参数：p : Ideal R；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`：card_stabilizer_eq_ca
rd_inertia_mul_finrank (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p] [P
.IsPrime] [PerfectField p.ResidueField]…
· 使用定理 `Algebra.IsInvariant.orbit_eq_primesOver`：orbit_eq_primesOver [Finite G] 
[SMulCommClass G A B] (P : Ideal A) (Q : Ideal B) [hP : Q.LiesOver P] [hQ : Q.Is
Prime] : MulAction.orbit G Q …
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) * P.inertiaDeg R = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank p P,
    ← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The cardinality of the inertia group is equal to the ramification index. -/
/-
**Ideal.card_inertia_eq_ramificationIdxIn** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S] [Module.Finite
 R S] [Flat R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPri
me] [PerfectField p.ResidueField] : Nat.card (P.inertia G) = Ideal.ramificationI
dxIn p S
参数：p : Ideal R；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank`：ncard_primesOver_mu
l_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p
] [P.IsPrime] [PerfectField p.ResidueFiel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`：ncard_pri
mesOver_mul_ramificationIdxIn_mul_inertiaDegIn : (primesOver p B).ncard * (ramif
icationIdxIn p B * inertiaDegIn p B) = Nat.card G

--- 原说明 ---
The cardinality of the inertia group is equal to the ramification index.
-/
lemma card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S ≠ 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

/-- The cardinality of the decomposition group is equal to the ramification index times the
inertia degree. -/
/-
**Ideal.card_stabilizer_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：card_stabilizer_eq [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S
] (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime] [PerfectFie
ld p.ResidueField] : Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S
 * p.inertiaDegIn S
参数：p : Ideal R；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`：card_stabilizer_eq_ca
rd_inertia_mul_finrank (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p] [P
.IsPrime] [PerfectField p.ResidueField]…
· 使用引理 `Ideal.card_inertia_eq_ramificationIdxIn`：card_inertia_eq_ramificationIdx
In [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S] (p : Ideal R) (P : I
deal S) [P.LiesOver p] [p.IsP…
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A

--- 原说明 ---
The cardinality of the decomposition group is equal to the ramification index ti
mes the
inertia degree.
-/
lemma card_stabilizer_eq [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [card_stabilizer_eq_card_inertia_mul_finrank p P, card_inertia_eq_ramificationIdxIn p,
    inertiaDegIn_eq_inertiaDeg p P G]

end inertia

section galRestrict

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

/-
**Ideal.exists_comap_galRestrict_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal
 R} {P₁ P₂ : Ideal S} (hP₁ : P₁ in primesOver p S) (hP₂ : P₂ in primesOver p S) 
: exists σ, P₁.comap (galRestrict R K L S σ) = P₂
参数：hP₁ : P₁ in primesOver p S；hP₂ : P₂ in primesOver p S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsIntegralClosure.finite`：IsIntegralClosure.finite [IsIntegrallyClosed A
] [IsNoetherianRing A] : Module.Finite A C
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGaloisGroup.of_isFractionRing`：IsGaloisGroup.of_isFractionRing [hGKL :
 IsGaloisGroup G K L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGalois
Group G A B
· 使用定理 `instSMulDistribClassAlgEquiv`：∀ (A : Type u_1) (K : Type u_2) (L : Type 
u_3) (B : Type u_4) [inst : CommRing A] [inst_1 : CommRing B]   [inst_2 : Field 
K] [inst_3 : Field…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Ideal.exists_smul_eq_of_isGaloisGroup`：exists_smul_eq_of_isGaloisGroup :
 exists σ : G, σ • P = Q
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `Ideal.comap_map_of_bijective`：comap_map_of_bijective : (I.map f).comap f
 = I
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
    {P₁ P₂ : Ideal S} (hP₁ : P₁ ∈ primesOver p S) (hP₂ : P₂ ∈ primesOver p S) :
    ∃ σ, P₁.comap (galRestrict R K L S σ) = P₂ := by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := hP₂.2
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let : MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  have : IsGaloisGroup Gal(L/K) R S := IsGaloisGroup.of_isFractionRing _ _ _ K L
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P₂ P₁ Gal(L/K)
  exact ⟨σ, comap_map_of_bijective _ ((galRestrict R K L S σ).bijective)⟩

end galRestrict

end Ideal

