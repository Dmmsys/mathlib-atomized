/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

## Main results
- `Ring.HasFiniteQuotients.instDimensionLEOne`: A ring with finite quotients has dimension `≤ 1`.
- `Ring.HasFiniteQuotients.instIsNoetherianRing` : A ring with finite quotients is noetherian.
- `Ring.HasFiniteQuotients.of_module_finite`: Assume that `R` has finite quotients and that `S` is
  a domain and a finite `R`-module. Then `S` has finite quotients.
- `Ring.HasFiniteQuotients.instOfIsDomainOfFG`: A domain that is also a finite `ℤ`-module
  has finite quotients.

-/

public section

/--
A ring `R` has finite quotients if the quotient `R ⧸ I` is finite for all nonzero ideals of `R`.
-/
/-
**Ring.HasFiniteQuotients** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ring`。
形式化陈述：(R : Type u_1) → [CommRing R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring `R` has finite quotients if the quotient `R ⧸ I` is finite for all nonzer
o ideals of `R`.
-/
class Ring.HasFiniteQuotients (R : Type*) [CommRing R] : Prop where
  finiteQuotient {I : Ideal R} : I ≠ ⊥ → Finite (R ⧸ I)

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R]

/-- A finite ring has finite quotients. -/
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite ring has finite quotients.
-/
instance [Finite R] : Ring.HasFiniteQuotients R where
  finiteQuotient := fun _ ↦ Quotient.finite _

section properties

variable [HasFiniteQuotients R]

/-- A nonzero prime ideal of a ring with finite quotients is maximal. -/
/-
**Ring.HasFiniteQuotients.maximalOfPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ring.HasFini
teQuotients`。
形式化陈述：maximalOfPrime {P : Ideal R} [P.IsPrime] (hp : P != ⊥) : P.IsMaximal
参数：hp : P != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `Ideal.Quotient.maximal_of_isField`：maximal_of_isField {R} [CommRing R] (
I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal
· 使用定理 `Finite.isField_of_domain`：Finite.isField_of_domain (R) [CommRing R] [IsD
omain R] [Finite R] : IsField R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
A nonzero prime ideal of a ring with finite quotients is maximal.
-/
theorem maximalOfPrime {P : Ideal R} [P.IsPrime] (hp : P ≠ ⊥) :
    P.IsMaximal :=
  have : Finite (R ⧸ P) := finiteQuotient hp
  Ideal.Quotient.maximal_of_isField P <| Finite.isField_of_domain (R ⧸ P)

/-- A ring with finite quotients has dimension `≤ 1`. -/
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring with finite quotients has dimension `≤ 1`.
-/
instance : DimensionLEOne R where
  maximalOfPrime := fun h _ ↦ maximalOfPrime h

/-- A ring with finite quotients is noetherian. -/
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring with finite quotients is noetherian.
-/
instance : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Submodule.fg_span_singleton x
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] [PerfectField (FractionRing R)] (P : Ideal R) [P.IsPrime] :
    PerfectField P.ResidueField := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R _).toRingEquiv
  · have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    infer_instance
/-
**Ring.HasFiniteQuotients.cardQuot_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ring.HasFinite
Quotients`。
形式化陈述：cardQuot_pos (I : Ideal R) (hI : I != ⊥) : 0 < I.cardQuot
参数：I : Ideal R；hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.cardQuot_apply`：cardQuot_apply (S : Submodule R M) : cardQuot 
S = Nat.card (M ⧸ S)
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Ideal.Quotient.instNonemptyQuotient`：∀ {R : Type u} [inst : Ring R] {I :
 Ideal R} [I.IsTwoSided], Nonempty (R ⧸ I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem cardQuot_pos (I : Ideal R) (hI : I ≠ ⊥) : 0 < I.cardQuot := by
  have := finiteQuotient hI
  rw [Submodule.cardQuot_apply]
  exact Nat.card_pos
/-
**Ring.HasFiniteQuotients.finite_setOfPred_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ring.H
asFiniteQuotients`。
形式化陈述：finite_setOfPred_mem (x : R) (hx : x != 0) : {I : Ideal R | x in I}.Finite
参数：x : R；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
theorem finite_setOfPred_mem (x : R) (hx : x ≠ 0) : {I : Ideal R | x ∈ I}.Finite := by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ ≤ I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

@[deprecated (since := "2026-07-09")] alias finite_setOf_mem := finite_setOfPred_mem

open scoped Pointwise in
/-- For every bound `B`, a ring with finite quotients has only finitely many ideals of norm bounded
by `B`. -/
/-
**Ring.HasFiniteQuotients.finite_cardQuot_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring.Has
FiniteQuotients`。
形式化陈述：finite_cardQuot_le (B : Nat) : {I : Ideal R | I.cardQuot <= B}.Finite
参数：B : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `Infinite.exists_subset_card_eq`：exists_subset_card_eq (α : Type*) [Infin
ite α] (n : Nat) : exists s : Finset α, #s = n
· 使用定理 `Set.Finite.of_sdiff`：∀ {α : Type u} {s t : Set α}, (s \ t).Finite → t.Fi
nite → s.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.cardQuot_apply`：cardQuot_apply (S : Submodule R M) : cardQuot 
S = Nat.card (M ⧸ S)
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `Finset.exists_ne_map_eq_of_card_image_lt`：exists_ne_map_eq_of_card_image
_lt [DecidableEq β] {f : α -> β} (hc : #(s.image f) < #s) : exists x in s, exist
s y in s, x != y ∧ f x = f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.mem_sub`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Sub α]
 {s t : Finset α} {a : α},   a ∈ s - t ↔ ∃ b ∈ s, ∃ c ∈ t, b - c = a
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
For every bound `B`, a ring with finite quotients has only finitely many ideals 
of norm bounded
by `B`.
-/
theorem finite_cardQuot_le (B : ℕ) : {I : Ideal R | I.cardQuot ≤ B}.Finite := by
  classical
  rcases finite_or_infinite R
  · apply Set.toFinite
  -- if `R` is infinite, then we can pick a finite set `s` of cardinality `B + 1`
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R (B + 1)
  -- and consider the finite set `t` of nonzero differences
  let t := (s - s) \ {0}
  refine Set.Finite.of_sdiff ?_ (Set.finite_singleton ⊥)
  -- in a ring with finite quotients, each nonzero element is contained in only finitely many ideals
  -- so it is enough to show that each ideal `I` of norm at most `B` contains some element of `t`
  suffices {I | Submodule.cardQuot I ≤ B} \ {⊥} ⊆ ⋃ x ∈ t, {I | x ∈ I} from
    (t.finite_toSet.biUnion fun x hx ↦ finite_setOfPred_mem x (by grind)).subset this
  intro I hI
  rw [Set.mem_sdiff, Set.mem_ofPred, Submodule.cardQuot_apply] at hI
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
  -- `s` has cardinality `B + 1`, but the quotient `R ⧸ I` has cardinality at most `B`
  replace hs : (s.image (Ideal.Quotient.mk I)).card < s.card := by
    have := finiteQuotient hI.2
    have := Fintype.ofFinite (R ⧸ I)
    grw [Finset.card_le_univ, Fintype.card_eq_nat_card, hI.1, hs, Nat.lt_add_one_iff]
  -- so we can find distinct `x, y ∈ s` with the desired collision `x - y ∈ I`
  obtain ⟨x, hx, y, hy, hxy, h⟩ := Finset.exists_ne_map_eq_of_card_image_lt hs
  refine ⟨x - y, ?_, (Submodule.Quotient.eq I).mp h⟩
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
  rwa [Finset.notMem_singleton, sub_ne_zero]

/-- A ring with finite quotients has only finitely many ideals of bounded norm. -/
/-
**Ring.HasFiniteQuotients.finite_absNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring.HasF
initeQuotients`。
形式化陈述：finite_absNorm_le [IsDedekindDomain R] [Module.Free Int R] (B : Nat) : {I 
: Ideal R | I.absNorm <= B}.Finite
参数：B : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.HasFiniteQuotients.finite_cardQuot_le`：finite_cardQuot_le (B : Nat)
 : {I : Ideal R | I.cardQuot <= B}.Finite

--- 原说明 ---
A ring with finite quotients has only finitely many ideals of bounded norm.
-/
theorem finite_absNorm_le [IsDedekindDomain R] [Module.Free ℤ R] (B : ℕ) :
    {I : Ideal R | I.absNorm ≤ B}.Finite :=
  finite_cardQuot_le B

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
/-
**Ring.HasFiniteQuotients.finite_cardQuot_heightOneSpectrum_le** 是 Mathlib 中的一个定
理，位于命名空间 `Ring.HasFiniteQuotients`。
形式化陈述：finite_cardQuot_heightOneSpectrum_le (B : Nat) : {p : IsDedekindDomain.Hei
ghtOneSpectrum R | p.asIdeal.cardQuot <= B}.Finite
参数：B : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_injOn`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α}
 {t : Set β}, Set.MapsTo f s t → Set.InjOn f s → t.Finite → s.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ext`：∀ {R : Type u_1} {inst : CommRin
g R} {x y : IsDedekindDomain.HeightOneSpectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ring.HasFiniteQuotients.finite_cardQuot_le`：finite_cardQuot_le (B : Nat)
 : {I : Ideal R | I.cardQuot <= B}.Finite

--- 原说明 ---
A ring with finite quotients has only finitely many nonzero prime ideals of boun
ded norm.
-/
theorem finite_cardQuot_heightOneSpectrum_le (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.cardQuot ≤ B}.Finite :=
  (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ ↦ IsDedekindDomain.HeightOneSpectrum.ext)

/-- A ring with finite quotients has only finitely many nonzero prime ideals of bounded norm. -/
/-
**Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le** 是 Mathlib 中的一个定理
，位于命名空间 `Ring.HasFiniteQuotients`。
形式化陈述：finite_absNorm_heightOneSpectrum_le [IsDedekindDomain R] [Module.Free Int 
R] (B : Nat) : {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.absNorm <= 
B}.Finite
参数：B : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.HasFiniteQuotients.finite_cardQuot_heightOneSpectrum_le`：finite_car
dQuot_heightOneSpectrum_le (B : Nat) : {p : IsDedekindDomain.HeightOneSpectrum R
 | p.asIdeal.cardQuot <= B}.Finite

--- 原说明 ---
A ring with finite quotients has only finitely many nonzero prime ideals of boun
ded norm.
-/
theorem finite_absNorm_heightOneSpectrum_le [IsDedekindDomain R] [Module.Free ℤ R] (B : ℕ) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.absNorm ≤ B}.Finite :=
  finite_cardQuot_heightOneSpectrum_le B
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Northcott fun p : Ideal R ↦ p.cardQuot :=
  ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDedekindDomain R] [Module.Free ℤ R] :
    Northcott fun p : IsDedekindDomain.HeightOneSpectrum R ↦ p.asIdeal.absNorm :=
  ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

variable (R) in
/--
Assume that `R` has finite quotients and that `S` is a domain and a finite `R`-module. Then
`S` has finite quotients.
-/
/-
**Ring.HasFiniteQuotients.of_module_finite** 是 Mathlib 中的一个定理，位于命名空间 `Ring.HasFi
niteQuotients`。
形式化陈述：of_module_finite (S : Type*) [CommRing S] [IsDomain S] [Algebra R S] [Modu
le.Finite R S] : HasFiniteQuotients S where finiteQuotient {I} hI
参数：S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `Ideal.under_ne_bot`：under_ne_bot [Nontrivial A] [IsDomain B] (hP : P != 
⊥) : under A P != ⊥
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Assume that `R` has finite quotients and that `S` is a domain and a finite `R`-m
odule. Then
`S` has finite quotients.
-/
theorem of_module_finite (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] :
    HasFiniteQuotients S where
  finiteQuotient {I} hI := by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
    have : Finite (R ⧸ J) := finiteQuotient <| Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ J)

end properties

/-- The ring `ℤ` has finite quotients. -/
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `ℤ` has finite quotients.
-/
instance : HasFiniteQuotients ℤ where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
    exact inferInstanceAs <| Finite (ℤ ⧸ Ideal.span {n})

/-- A domain that is finitely generated has finite quotients. -/
/-
**Ring.HasFiniteQuotients.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.HasFiniteQuotients`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A domain that is finitely generated has finite quotients.
-/
instance [IsDomain R] [Module.Finite ℤ R] : HasFiniteQuotients R :=
  .of_module_finite ℤ R

end Ring.HasFiniteQuotients

