/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going down

In this file we define a predicate `Algebra.HasGoingDown`: An `R`-algebra `S` satisfies
`Algebra.HasGoingDown R S` if for every pair of prime ideals `p ≤ q` of `R` with `Q` a prime
of `S` lying above `q`, there exists a prime `P ≤ Q` of `S` lying above `p`.

## Main results

- `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`: going down is equivalent
  to generalizations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingDown.of_flat`: flat algebras satisfy going down.

## Note

- For the fact that an integral extension of domains with normal base satisfies going down,
  see `Mathlib/RingTheory/IntegralClosure/GoingDown.lean`.

-/

@[expose] public section

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingDown R S` if for every pair of
prime ideals `p ≤ q` of `R` with `Q` a prime of `S` lying above `q`, there exists a
prime `P ≤ Q` of `S` lying above `p`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_le_liesOver_of_le` for applying it.
-/
@[stacks 00HV "(2)"]
/-
**Algebra.HasGoingDown** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `S` satisfies `Algebra.HasGoingDown R S` if for every pair of
prime ideals `p ≤ q` of `R` with `Q` a prime of `S` lying above `q`, there exist
s a
prime `P ≤ Q` of `S` lying above `p`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_le_liesOver_of_le` for applying it.
-/
class Algebra.HasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_le_liesOver_of_lt {p : Ideal R} [p.IsPrime] (Q : Ideal S) [Q.IsPrime] :
    p < Q.under R → ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
/-
**Ideal.exists_ideal_le_liesOver_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_ideal_le_liesOver_of_le [Algebra.HasGoingDown R S] {p q : Ide
al R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] (hle : p 
<= q) : exists P <= Q, P.IsPrime ∧ P.LiesOver p
参数：Q : Ideal S；hle : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt`：∀ {R : Type u_1} {S
 : Type u_2} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   
[self : Algebra.HasGoingDown R S] {p : Id…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Ideal.exists_ideal_le_liesOver_of_le [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hle : p ≤ q) :
    ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p := by
  by_cases h : p = q
  · subst h
    use Q
  · have := Q.over_def q
    subst this
    exact Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle h)
/-
**Ideal.exists_ideal_lt_liesOver_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_ideal_lt_liesOver_of_lt [Algebra.HasGoingDown R S] {p q : Ide
al R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] (hpq : p 
< q) : exists P < Q, P.IsPrime ∧ P.LiesOver p
参数：Q : Ideal S；hpq : p < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_ideal_le_liesOver_of_le`：Ideal.exists_ideal_le_liesOver_of_
le [Algebra.HasGoingDown R S] {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal
 S) [Q.IsPrime] [Q.LiesOve…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
lemma Ideal.exists_ideal_lt_liesOver_of_lt [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hpq : p < q) : ∃ P < Q, P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, hPQ, _, _⟩ := Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨P, ?_, inferInstance, inferInstance⟩
  by_contra hc
  have : P = Q := eq_of_le_of_not_lt hPQ hc
  subst this
  simp [P.over_def p, P.over_def q] at hpq

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.exists_ltSeries_of_hasGoingDown** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_ltSeries_of_hasGoingDown [Algebra.HasGoingDown R S] (l : LTSe
ries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver l.last.asIdea
l] : exists (L : LTSeries (PrimeSpectrum S)), L.length = l.length ∧ L.last = ⟨P,
 inferInstance⟩ ∧ List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.t
oList
参数：l : LTSeries (PrimeSpectrum R)；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.singleton_length`：∀ {α : Type u_1} (r : SetRel α α) (a : α), (
RelSeries.singleton r a).length = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RelSeries.last_singleton`：last_singleton {r : SetRel α α} (x : α) : (sin
gleton r x).last = x
· 使用引理 `RelSeries.toList_singleton`：toList_singleton (x : α) : (singleton r x).t
oList = [x]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `RelSeries.last_cons`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).last = p.la
st
· 使用引理 `RelSeries.toList_getElem_zero_eq_head`：toList_getElem_zero_eq_head (p : 
RelSeries r) : p.toList[0] = p.head
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RelSeries.length_toList`：length_toList (x : RelSeries r) : x.toList.leng
th = x.length + 1
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 39 条，此处仅展示前 30 条）
-/
lemma Ideal.exists_ltSeries_of_hasGoingDown [Algebra.HasGoingDown R S]
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver l.last.asIdeal] :
    ∃ (L : LTSeries (PrimeSpectrum S)),
      L.length = l.length ∧
      L.last = ⟨P, inferInstance⟩ ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.last_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
    ext : 1
    simpa using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.last_cons] at lo
    obtain ⟨L, len, last, spec⟩ := ih P
    have : L.head.asIdeal.LiesOver l.head.asIdeal := by
      constructor
      rw [← L.toList_getElem_zero_eq_head, ← l.toList_getElem_zero_eq_head, Ideal.under_def]
      have : l.toList[0] = (PrimeSpectrum.comap (algebraMap R S)) L.toList[0] := by
        rw [List.getElem_map_rev (PrimeSpectrum.comap (algebraMap R S)),
          List.getElem_of_eq spec.symm _]
      rwa [PrimeSpectrum.ext_iff] at this
    obtain ⟨Q, Qlt, hQ, Qlo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt L.head.asIdeal lt
    use L.cons ⟨Q, hQ⟩ Qlt
    simp only [RelSeries.cons_length, add_left_inj, RelSeries.last_cons]
    exact ⟨len, last, by simpa [spec] using PrimeSpectrum.ext_iff.mpr Qlo.over.symm⟩

namespace Algebra.HasGoingDown

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going down property if and only if generalizations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(1)"]
/-
**Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.HasGoingDown`。
形式化陈述：iff_generalizingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ Genera
lizingMap (PrimeSpectrum.comap (algebraMap R S))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_ideal_le_liesOver_of_le`：Ideal.exists_ideal_le_liesOver_of_
le [Algebra.HasGoingDown R S] {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal
 S) [Q.IsPrime] [Q.LiesOve…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
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
An `R`-algebra `S` has the going down property if and only if generalizations li
ft
along `Spec S → Spec R`.
-/
lemma iff_generalizingMap_primeSpectrumComap :
    Algebra.HasGoingDown R S ↔
      GeneralizingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h ↦ ⟨fun {p} hp Q hQ hlt ↦ ?_⟩⟩
  · intro h Q p hp
    rw [← PrimeSpectrum.le_iff_specializes] at hp
    obtain ⟨P, hle, hP, h⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le (p := p.asIdeal)
      (q := Q.asIdeal.under R) hp
    refine ⟨⟨P, hP⟩, (PrimeSpectrum.le_iff_specializes _ Q).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : (⟨p, hp⟩ : PrimeSpectrum R) ⤳ (PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQ⟩) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨P, hs, heq⟩ := h this
    refine ⟨P.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, P.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
/-
**Algebra.HasGoingDown.trans** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.HasGoingDown`。
形式化陈述：trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower 
R S T] [Algebra.HasGoingDown R S] [Algebra.HasGoingDown S T] : Algebra.HasGoingD
own R T
参数：T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`：iff_general
izingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ GeneralizingMap (PrimeS
pectrum.comap (algebraMap R S))
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用引理 `GeneralizingMap.comp`：GeneralizingMap.comp {f : X -> Y} {g : Y -> Z} (hf
 : GeneralizingMap f) (hg : GeneralizingMap g) : GeneralizingMap (g ∘ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingDown R S] [Algebra.HasGoingDown S T] :
    Algebra.HasGoingDown R T := by
  rw [iff_generalizingMap_primeSpectrumComap, IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply GeneralizingMap.comp
  · rwa [← iff_generalizingMap_primeSpectrumComap]
  · rwa [← iff_generalizingMap_primeSpectrumComap]

/-- If for every prime of `S`, the map `Spec Sₚ → Spec Rₚ` is surjective,
the algebra satisfies going down. -/
/-
**Algebra.HasGoingDown.of_comap_localRingHom_surjective** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.HasGoingDown`。
形式化陈述：of_comap_localRingHom_surjective (H : forall (P : Ideal S) [P.IsPrime], Fu
nction.Surjective (PrimeSpectrum.comap <| Localization.localRingHom (P.under R) 
P (algebraMap R S) rfl)) : Algebra.HasGoingDown R S where exists_ideal_le_liesOv
er_of_lt {p} _ Q _ hlt
参数：H : forall (P : Ideal S) [P.IsPrime], Function.Surjective (PrimeSpectrum.coma
p <| Localization.localRingHom (P.under R) P (algebraMap R S) rfl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用引理 `Ideal.isPrime_map_of_isLocalizationAtPrime`：Ideal.isPrime_map_of_isLocal
izationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) : (p.map (algebraMap R S
)).IsPrime
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用引理 `Ideal.under_map_of_isLocalizationAtPrime`：Ideal.under_map_of_isLocalizat
ionAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) : (p.map (algebraMap R S)).u
nder R = p

--- 原说明 ---
If for every prime of `S`, the map `Spec Sₚ → Spec Rₚ` is surjective,
the algebra satisfies going down.
-/
lemma of_comap_localRingHom_surjective
    (H : ∀ (P : Ideal S) [P.IsPrime], Function.Surjective
      (PrimeSpectrum.comap <| Localization.localRingHom (P.under R) P (algebraMap R S) rfl)) :
    Algebra.HasGoingDown R S where
  exists_ideal_le_liesOver_of_lt {p} _ Q _ hlt := by
    let pl : Ideal (Localization.AtPrime <| Q.under R) := p.map (algebraMap R _)
    have : pl.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime (Q.under R) hlt.le
    obtain ⟨⟨Pl, _⟩, hl⟩ := H Q ⟨pl, inferInstance⟩
    refine ⟨Pl.under S, ?_, Ideal.IsPrime.under S Pl, ⟨?_⟩⟩
    · exact (IsLocalization.AtPrime.orderIsoOfPrime _ Q ⟨Pl, inferInstance⟩).2.2
    · let := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
      replace hl : Pl.under _ = pl := by simpa [PrimeSpectrum.ext_iff] using! hl
      rw [Ideal.under_under, ← Ideal.under_under (B := (Localization.AtPrime <| Q.under R)) Pl, hl,
        Ideal.under_map_of_isLocalizationAtPrime (Q.under R) hlt.le]

/-- Flat algebras satisfy the going down property. -/
@[stacks 00HS]
/-
**Algebra.HasGoingDown.of_flat** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.HasGoingDown`。
形式化陈述：of_flat [Module.Flat R S] : Algebra.HasGoingDown R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.HasGoingDown.of_comap_localRingHom_surjective`：of_comap_localRin
gHom_surjective (H : forall (P : Ideal S) [P.IsPrime], Function.Surjective (Prim
eSpectrum.comap <| Localization.localRingHo…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `Localization.isLocalHom_localRingHom`：isLocalHom_localRingHom (J : Ideal
 P) [hJ : J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) : IsLocalHom (localRin
gHom I J f hIJ)
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用引理 `Module.FaithfullyFlat.of_flat_of_isLocalHom`：Module.FaithfullyFlat.of_fl
at_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B] [IsLocalHom (algebra
Map A B)] : Module.FaithfullyFlat…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `instFlatAtPrimeOfIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u_5} [ins
t : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] [Module.Flat A B]  
 (p : Ideal A) [inst_4 :…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用引理 `PrimeSpectrum.comap_surjective_of_faithfullyFlat`：PrimeSpectrum.comap_su
rjective_of_faithfullyFlat : Function.Surjective (comap (algebraMap A B))

--- 原说明 ---
Flat algebras satisfy the going down property.
-/
instance of_flat [Module.Flat R S] : Algebra.HasGoingDown R S := by
  apply of_comap_localRingHom_surjective
  intro P hP
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : IsLocalHom (algebraMap (Localization.AtPrime <| P.under R) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom (P.under R) P (algebraMap R S) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime (P.under R)) (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Algebra.HasGoingDown

