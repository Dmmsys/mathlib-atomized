/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going up

In this file we define a predicate `Algebra.HasGoingUp`: An `R`-algebra `S` satisfies
`Algebra.HasGoingUp R S` if for every pair of prime ideals `p ≤ q` of `R` with
`P` a prime of `S` lying above `p`, there exists a prime `P ≤ Q` of `S` lying above `q`.

This file closely mirrors `Mathlib.RingTheory.Ideal.GoingDown`.

## Main results

- `Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap`: going up is equivalent
  to specializations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingUp.of_isIntegral`: integral algebras satisfy going up.
-/

@[expose] public section

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingUp R S` if for every pair of
prime ideals `p ≤ q` of `R` with `P` a prime of `S` lying above `p`, there exists a
prime `P ≤ Q` of `S` lying above `q`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_ge_liesOver_of_le` for applying it. -/
@[stacks 00HV "(1)"]
/-
**Algebra.HasGoingUp** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `S` satisfies `Algebra.HasGoingUp R S` if for every pair of
prime ideals `p ≤ q` of `R` with `P` a prime of `S` lying above `p`, there exist
s a
prime `P ≤ Q` of `S` lying above `q`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_ge_liesOver_of_le` for applying it.
-/
class Algebra.HasGoingUp
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_ge_liesOver_of_lt {q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] :
    P.under R < q → ∃ Q, P ≤ Q ∧ Q.IsPrime ∧ Q.LiesOver q

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Ideal

/-
**Ideal.exists_ideal_ge_liesOver_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_ideal_ge_liesOver_of_le [Algebra.HasGoingUp R S] {p q : Ideal R} [q
.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hle : p <= q) : exists Q, P 
<= Q ∧ Q.IsPrime ∧ Q.LiesOver q
参数：P : Ideal S；hle : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt`：∀ {R : Type u_1} {S :
 Type u_2} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [s
elf : Algebra.HasGoingUp R S] {q : Idea…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
lemma exists_ideal_ge_liesOver_of_le [Algebra.HasGoingUp R S]
    {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hle : p ≤ q) :
    ∃ Q, P ≤ Q ∧ Q.IsPrime ∧ Q.LiesOver q := by
  rcases eq_or_ne p q with rfl | h
  · use P
  · rw [P.over_def p] at hle h
    exact Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt P (lt_of_le_of_ne hle h)
/-
**Ideal.exists_ideal_gt_liesOver_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_ideal_gt_liesOver_of_lt [Algebra.HasGoingUp R S] {p q : Ideal R} [q
.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hpq : p < q) : exists Q, P <
 Q ∧ Q.IsPrime ∧ Q.LiesOver q
参数：P : Ideal S；hpq : p < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_ideal_ge_liesOver_of_le`：exists_ideal_ge_liesOver_of_le [Al
gebra.HasGoingUp R S] {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.L
iesOver p] (hle : p <= q) …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
lemma exists_ideal_gt_liesOver_of_lt [Algebra.HasGoingUp R S]
    {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hpq : p < q) :
    ∃ Q, P < Q ∧ Q.IsPrime ∧ Q.LiesOver q := by
  obtain ⟨Q, hPQ, hQ, hQq⟩ := P.exists_ideal_ge_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨Q, lt_of_le_of_ne hPQ fun h ↦ ?_, hQ, hQq⟩
  subst Q
  simp [P.over_def p, P.over_def q] at hpq

/-- This generalizes `exists_ideal_over_prime_of_isIntegral_of_isPrime`
to arbitrary length chains. -/
/-
**Ideal.exists_ltSeries_of_hasGoingUp** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_ltSeries_of_hasGoingUp [Algebra.HasGoingUp R S] (l : LTSeries (Prim
eSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver (RelSeries.head l).asId
eal] : exists L : LTSeries (PrimeSpectrum S), L.length = l.length ∧ L.head = (⟨P
, inferInstance⟩ : PrimeSpectrum S) ∧ List.map (PrimeSpectrum.comap (algebraMap 
R S)) (L.toList) = l.toList
参数：l : LTSeries (PrimeSpectrum R)；P : Ideal S；RelSeries.head l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.toList_singleton`：toList_singleton (x : α) : (singleton r x).t
oList = [x]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `RelSeries.head_singleton`：head_singleton {r : SetRel α α} (x : α) : (sin
gleton r x).head = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用引理 `Ideal.exists_ideal_gt_liesOver_of_lt`：exists_ideal_gt_liesOver_of_lt [Al
gebra.HasGoingUp R S] {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.L
iesOver p] (hpq : p < q) :…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `RelSeries.cons_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).length = 
p.length + …
· 使用引理 `RelSeries.toList_cons`：toList_cons (p : RelSeries r) (x : α) (hx : x ~[r
] p.head) : (p.cons x hx).toList = x :: p.toList

--- 原说明 ---
This generalizes `exists_ideal_over_prime_of_isIntegral_of_isPrime`
to arbitrary length chains.
-/
lemma exists_ltSeries_of_hasGoingUp [Algebra.HasGoingUp R S]
    (l : LTSeries (PrimeSpectrum R))
    (P : Ideal S) [P.IsPrime]
    [lo : P.LiesOver (RelSeries.head l).asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      L.head = (⟨P, inferInstance⟩ : PrimeSpectrum S) ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) (L.toList) = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    refine ⟨RelSeries.singleton _ ⟨P, inferInstance⟩, rfl, rfl, ?_⟩
    simpa [PrimeSpectrum.ext_iff] using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.head_cons] at lo
    obtain ⟨Q, PQlt, hQ, Qlo⟩ :=
      Ideal.exists_ideal_gt_liesOver_of_lt P lt
    obtain ⟨L, len, head, spec⟩ := ih Q
    refine ⟨L.cons ⟨P, inferInstance⟩ (by
      simp_all only [Set.mem_ofPred_eq]
      exact PQlt), by simpa using len, rfl, ?_⟩
    simpa [spec, PrimeSpectrum.ext_iff] using lo.over.symm

end Ideal

namespace Algebra.HasGoingUp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going up property if and only if specializations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(2)"]
/-
**Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.HasGoingUp`。
形式化陈述：iff_specializingMap_primeSpectrumComap : Algebra.HasGoingUp R S ↔ Speciali
zingMap (PrimeSpectrum.comap (algebraMap R S))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_ideal_ge_liesOver_of_le`：exists_ideal_ge_liesOver_of_le [Al
gebra.HasGoingUp R S] {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.L
iesOver p] (hle : p <= q) …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
An `R`-algebra `S` has the going up property if and only if specializations lift
along `Spec S → Spec R`.
-/
lemma iff_specializingMap_primeSpectrumComap :
    Algebra.HasGoingUp R S ↔
      SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h ↦ ⟨fun {q} hq P hP hlt ↦ ?_⟩⟩
  · intro h P q hq
    simp only [flip] at hq
    rw [← PrimeSpectrum.le_iff_specializes] at hq
    obtain ⟨Q, hle, hQ, h⟩ := P.asIdeal.exists_ideal_ge_liesOver_of_le (q := q.asIdeal)
      (p := P.asIdeal.under R) hq
    refine ⟨⟨Q, hQ⟩, (PrimeSpectrum.le_iff_specializes P _).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : PrimeSpectrum.comap (algebraMap R S) ⟨P, hP⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨Q, hs, heq⟩ := h this
    refine ⟨Q.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, Q.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
/-
**Algebra.HasGoingUp.trans** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.HasGoingUp`。
形式化陈述：trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower 
R S T] [Algebra.HasGoingUp R S] [Algebra.HasGoingUp S T] : Algebra.HasGoingUp R 
T
参数：T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap`：iff_specializ
ingMap_primeSpectrumComap : Algebra.HasGoingUp R S ↔ SpecializingMap (PrimeSpect
rum.comap (algebraMap R S))
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用引理 `SpecializingMap.comp`：SpecializingMap.comp {f : X -> Y} {g : Y -> Z} (hf
 : SpecializingMap f) (hg : SpecializingMap g) : SpecializingMap (g ∘ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingUp R S] [Algebra.HasGoingUp S T] :
    Algebra.HasGoingUp R T := by
  rw [iff_specializingMap_primeSpectrumComap, IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply SpecializingMap.comp
  · rwa [← iff_specializingMap_primeSpectrumComap]
  · rwa [← iff_specializingMap_primeSpectrumComap]

/-- Integral algebras satisfy the going up property. -/
@[stacks 00GU]
/-
**Algebra.HasGoingUp.of_isIntegral** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.HasGoingUp
`。
形式化陈述：of_isIntegral [Algebra.IsIntegral R S] : Algebra.HasGoingUp R S where exis
ts_ideal_ge_liesOver_of_lt {q} _ P _ hPq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`：exists_ideal_ove
r_prime_of_isIntegral_of_isPrime [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime
 P] (I : Ideal S) [IsPrime I] (hIP : I.comap…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Integral algebras satisfy the going up property.
-/
instance of_isIntegral [Algebra.IsIntegral R S] : Algebra.HasGoingUp R S where
  exists_ideal_ge_liesOver_of_lt {q} _ P _ hPq :=
    let ⟨Q, hPQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q P hPq.le
    ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩

end Algebra.HasGoingUp

