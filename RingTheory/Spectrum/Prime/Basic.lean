/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Prime spectrum of a commutative (semi)ring

For the Zariski topology, see `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `zeroLocus s`: The zero locus of a subset `s` of `R`
  is the subset of `PrimeSpectrum R` consisting of all prime ideals that contain `s`.
* `vanishingIdeal t`: The vanishing ideal of a subset `t` of `PrimeSpectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## References
* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
-/

@[expose] public section

-- A dividing line between this file and `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` is
-- that we should not depend on the Zariski topology here
assert_not_exists TopologicalSpace

noncomputable section

open scoped Pointwise

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]
variable {R S}

/-
**PrimeSpectrum.nonempty_iff_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：nonempty_iff_nontrivial : Nonempty (PrimeSpectrum R) ↔ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
-/
lemma nonempty_iff_nontrivial : Nonempty (PrimeSpectrum R) ↔ Nontrivial R := by
  refine ⟨fun ⟨p⟩ ↦ ⟨0, 1, fun h ↦ p.2.ne_top ?_⟩, fun h ↦ ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩
/-
**PrimeSpectrum.isEmpty_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：isEmpty_iff_subsingleton : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.nonempty_iff_nontrivial`：nonempty_iff_nontrivial : Nonempt
y (PrimeSpectrum R) ↔ Nontrivial R
-/
lemma isEmpty_iff_subsingleton : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  contrapose!; exact nonempty_iff_nontrivial
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nonempty <| PrimeSpectrum R :=
  nonempty_iff_nontrivial.mpr inferInstance

/-- The prime spectrum of the zero ring is empty. -/
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum of the zero ring is empty.
-/
instance [Subsingleton R] : IsEmpty (PrimeSpectrum R) :=
  isEmpty_iff_subsingleton.mpr inferInstance
/-
**PrimeSpectrum.nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：nontrivial (p : PrimeSpectrum R) : Nontrivial R
参数：p : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PrimeSpectrum.nonempty_iff_nontrivial`：nonempty_iff_nontrivial : Nonempt
y (PrimeSpectrum R) ↔ Nontrivial R
-/
lemma nontrivial (p : PrimeSpectrum R) : Nontrivial R :=
  nonempty_iff_nontrivial.mp ⟨p⟩

variable (R S)
/-
**PrimeSpectrum.range_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：range_asIdeal : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem range_asIdeal : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr <| hj ▸ j.isPrime,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

/-- The map from the direct sum of prime spectra to the prime spectrum of a direct product. -/
@[simp]
/-
**PrimeSpectrum.primeSpectrumProdOfSum** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`
。
形式化陈述：(R : Type u) →   (S : Type v) →     [inst : CommSemiring R] → [inst_1 : Co
mmSemiring S] → PrimeSpectrum R ⊕ PrimeSpectrum S → PrimeSpectrum (R × S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the direct sum of prime spectra to the prime spectrum of a direct p
roduct.
-/
def primeSpectrumProdOfSum : PrimeSpectrum R ⊕ PrimeSpectrum S → PrimeSpectrum (R × S)
  | Sum.inl ⟨I, _⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrime_ideal_prod_top⟩
  | Sum.inr ⟨J, _⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrime_ideal_prod_top'⟩

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
`R` and the prime spectrum of `S`. -/
/-
**PrimeSpectrum.primeSpectrumProd** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：primeSpectrumProd : PrimeSpectrum (R × S) ≃ PrimeSpectrum R oplus PrimeSpe
ctrum S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The prime spectrum of `R × S` is in bijection with the disjoint unions of the pr
ime spectrum of
`R` and the prime spectrum of `S`.
-/
noncomputable def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ PrimeSpectrum R ⊕ PrimeSpectrum S :=
  Equiv.symm <|
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases (Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)

variable {R S}

@[simp]
/-
**PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) : ((primeSpectrum
Prod R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤
参数：x : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  rfl

@[simp]
/-
**PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) : ((primeSpectrum
Prod R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal
参数：x : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  rfl

/-- The zero locus of a set `s` of elements of a commutative (semi)ring `R` is the set of all
prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the subset of
`PrimeSpectrum R` where all "functions" in `s` vanish simultaneously.
-/
/-
**PrimeSpectrum.zeroLocus** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus (s : Set R) : Set (PrimeSpectrum R)
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero locus of a set `s` of elements of a commutative (semi)ring `R` is the s
et of all
prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function on the prime spe
ctrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in 
the quotient ring
`R` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the sub
set of
`PrimeSpectrum R` where all "functions" in `s` vanish simultaneously.
-/
def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }

@[simp]
/-
**PrimeSpectrum.mem_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：mem_zeroLocus (x : PrimeSpectrum R) (s : Set R) : x in zeroLocus s ↔ s sub
seteq x.asIdeal
参数：x : PrimeSpectrum R；s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_zeroLocus (x : PrimeSpectrum R) (s : Set R) : x ∈ zeroLocus s ↔ s ⊆ x.asIdeal :=
  Iff.rfl

@[simp]
/-
**PrimeSpectrum.zeroLocus_span** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus 
s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus s := by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal

/-- The vanishing ideal of a set `t` of points of the prime spectrum of a commutative ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
/-
**PrimeSpectrum.vanishingIdeal** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R
参数：t : Set (PrimeSpectrum R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vanishing ideal of a set `t` of points of the prime spectrum of a commutativ
e ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spe
ctrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in 
the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly th
e ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ x ∈ t, x.asIdeal
/-
**PrimeSpectrum.coe_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：coe_vanishingIdeal (t : Set (PrimeSpectrum R)) : (vanishingIdeal t : Set R
) = { f : R | forall x in t, f in x.asIdeal }
参数：t : Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.vanishingIdeal.eq_1`：∀ {R : Type u} [inst : CommSemiring R
] (t : Set (PrimeSpectrum R)), PrimeSpectrum.vanishingIdeal t = ⨅ x ∈ t, x.asIde
al
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x ∈ t, f ∈ x.asIdeal } := by
  ext f
  rw [vanishingIdeal, SetLike.mem_coe, Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]
/-
**PrimeSpectrum.mem_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) : f in vanishingIde
al t ↔ forall x in t, f in x.asIdeal
参数：t : Set (PrimeSpectrum R)；f : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `PrimeSpectrum.coe_vanishingIdeal`：coe_vanishingIdeal (t : Set (PrimeSpec
trum R)) : (vanishingIdeal t : Set R) = { f : R | forall x in t, f in x.asIdeal 
}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x ∈ t, f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_ofPred_eq]

@[simp]
/-
**PrimeSpectrum.vanishingIdeal_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：vanishingIdeal_singleton (x : PrimeSpectrum R) : vanishingIdeal ({x} : Set
 (PrimeSpectrum R)) = x.asIdeal
参数：x : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vanishingIdeal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishingIdeal]
/-
**PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：subset_zeroLocus_iff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Id
eal R) : t subseteq zeroLocus I ↔ I <= vanishingIdeal t
参数：t : Set (PrimeSpectrum R)；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (PrimeSpec
trum R)) (f : R) : f in vanishingIdeal t ↔ forall x in t, f in x.asIdeal
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t ⊆ zeroLocus I ↔ I ≤ vanishingIdeal t :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

section Gc

variable (R)

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
/-
**PrimeSpectrum.gc** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => z
eroLocus I) fun t => vanishingIdeal t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal`：subset_zeroLocus_i
ff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) : t subseteq zero
Locus I ↔ I <= vanishingIdeal t

--- 原说明 ---
`zeroLocus` and `vanishingIdeal` form a Galois connection.
-/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

set_option backward.isDefEq.respectTransparency false in
/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
/-
**PrimeSpectrum.gc_set** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：gc_set : @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s =>
 zeroLocus s) fun t => vanishingIdeal t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `GaloisConnection.compose`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {l1 : α → β}   {u1 : 
β → α} {l2 : β…
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t

--- 原说明 ---
`zeroLocus` and `vanishingIdeal` form a Galois connection.
-/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)
/-
**PrimeSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal** 是 Mathlib 中的一个定理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s 
: Set R) : t subseteq zeroLocus s ↔ s subseteq vanishingIdeal t
参数：t : Set (PrimeSpectrum R)；s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t

end Gc

/-
**PrimeSpectrum.subset_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `Prime
Spectrum`。
形式化陈述：subset_vanishingIdeal_zeroLocus (s : Set R) : s subseteq vanishingIdeal (z
eroLocus s)
参数：s : Set R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s
/-
**PrimeSpectrum.le_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：le_vanishingIdeal_zeroLocus (I : Ideal R) : I <= vanishingIdeal (zeroLocus
 I)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I

@[simp]
/-
**PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical** 是 Mathlib 中的一个定理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLo
cus (I : Set R)) = I.radical
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (PrimeSpec
trum R)) (f : R) : f in vanishingIdeal t ↔ forall x in t, f in x.asIdeal
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishingIdeal, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩
/-
**PrimeSpectrum.nilradical_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：nilradical_eq_iInf : nilradical R = iInf asIdeal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.range_asIdeal`：range_asIdeal : Set.range PrimeSpectrum.asI
deal = {J : Ideal R | J.IsPrime}
-/
theorem nilradical_eq_iInf : nilradical R = iInf asIdeal := by
  apply range_asIdeal R ▸ nilradical_eq_sInf R
/-
**PrimeSpectrum.vanishingIdeal_univ** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R], PrimeSpectrum.vanishingIdeal Set.u
niv = nilradical R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.vanishingIdeal.eq_1`：∀ {R : Type u} [inst : CommSemiring R
] (t : Set (PrimeSpectrum R)), PrimeSpectrum.vanishingIdeal t = ⨅ x ∈ t, x.asIde
al
· 使用定理 `iInf_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α}, ⨅ x ∈ Set.univ, f x = ⨅ x, f x
· 使用定理 `PrimeSpectrum.nilradical_eq_iInf`：nilradical_eq_iInf : nilradical R = iI
nf asIdeal
-/
@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
  rw [vanishingIdeal, iInf_univ, nilradical_eq_iInf]

@[simp]
/-
**PrimeSpectrum.zeroLocus_radical** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocu
s I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
-/
theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I
/-
**PrimeSpectrum.subset_zeroLocus_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Prime
Spectrum`。
形式化陈述：subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) : t subseteq z
eroLocus (vanishingIdeal t)
参数：t : Set (PrimeSpectrum R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    t ⊆ zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t
/-
**PrimeSpectrum.zeroLocus_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_anti_mono {s t : Set R} (h : s subseteq t) : zeroLocus t subsete
q zeroLocus s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem zeroLocus_anti_mono {s t : Set R} (h : s ⊆ t) : zeroLocus t ⊆ zeroLocus s :=
  (gc_set R).monotone_l h
/-
**PrimeSpectrum.zeroLocus_anti_mono_ideal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s <= t) : zeroLocus (t : Se
t R) subseteq zeroLocus (s : Set R)
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) :
    zeroLocus (t : Set R) ⊆ zeroLocus (s : Set R) :=
  (gc R).monotone_l h
/-
**PrimeSpectrum.vanishingIdeal_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：vanishingIdeal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s subseteq t) 
: vanishingIdeal t <= vanishingIdeal s
参数：PrimeSpectrum R；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem vanishingIdeal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc R).monotone_u h
/-
**PrimeSpectrum.zeroLocus_subset_zeroLocus_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：zeroLocus_subset_zeroLocus_iff (I J : Ideal R) : zeroLocus (I : Set R) sub
seteq zeroLocus (J : Set R) ↔ J <= I.radical
参数：I J : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal`：subset_zeroLocus_i
ff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) : t subseteq zero
Locus I ↔ I <= vanishingIdeal t
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal R) :
    zeroLocus (I : Set R) ⊆ zeroLocus (J : Set R) ↔ J ≤ I.radical := by
  rw [subset_zeroLocus_iff_le_vanishingIdeal, vanishingIdeal_zeroLocus_eq_radical]
/-
**PrimeSpectrum.zeroLocus_subset_zeroLocus_singleton_iff** 是 Mathlib 中的一个定理，位于命名
空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_subset_zeroLocus_singleton_iff (f g : R) : zeroLocus ({f} : Set 
R) subseteq zeroLocus {g} ↔ g in (Ideal.span ({f} : Set R)).radical
参数：f g : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `PrimeSpectrum.zeroLocus_subset_zeroLocus_iff`：zeroLocus_subset_zeroLocus
_iff (I J : Ideal R) : zeroLocus (I : Set R) subseteq zeroLocus (J : Set R) ↔ J 
<= I.radical
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zeroLocus_subset_zeroLocus_singleton_iff (f g : R) :
    zeroLocus ({f} : Set R) ⊆ zeroLocus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical := by
  rw [← zeroLocus_span {f}, ← zeroLocus_span {g}, zeroLocus_subset_zeroLocus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]
/-
**PrimeSpectrum.zeroLocus_bot** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ :=
  (gc R).l_bot

@[simp]
/-
**PrimeSpectrum.zeroLocus_nilradical** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_nilradical : zeroLocus (nilradical R : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nilradical.eq_1`：∀ (R : Type u_3) [inst : CommSemiring R], nilradical R 
= Ideal.radical 0
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `PrimeSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : 
Set R) = Set.univ
-/
lemma zeroLocus_nilradical : zeroLocus (nilradical R : Set R) = Set.univ := by
  rw [nilradical, zeroLocus_radical, Ideal.zero_eq_bot, zeroLocus_bot]

@[simp]
/-
**PrimeSpectrum.zeroLocus_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：zeroLocus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : 
Set R) = Set.univ
-/
theorem zeroLocus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ :=
  zeroLocus_bot

@[simp]
/-
**PrimeSpectrum.zeroLocus_empty** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_empty : zeroLocus (∅ : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem zeroLocus_empty : zeroLocus (∅ : Set R) = Set.univ :=
  (gc_set R).l_bot

@[simp]
/-
**PrimeSpectrum.vanishingIdeal_empty** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：vanishingIdeal_empty : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem vanishingIdeal_empty : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using! (gc R).u_top
/-
**PrimeSpectrum.zeroLocus_empty_of_one_mem** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) in s) : zeroLocus s = 
∅
参数：h : (1 : R) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]
/-
**PrimeSpectrum.zeroLocus_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.zeroLocus_empty_of_one_mem`：zeroLocus_empty_of_one_mem {s 
: Set R} (h : (1 : R) in s) : zeroLocus s = ∅
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))
/-
**PrimeSpectrum.zeroLocus_empty_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I =
 ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `PrimeSpectrum.zeroLocus_empty_of_one_mem`：zeroLocus_empty_of_one_mem {s 
: Set R} (h : (1 : R) in s) : zeroLocus s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial

@[simp]
/-
**PrimeSpectrum.zeroLocus_univ** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_univ : zeroLocus (Set.univ : Set R) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.zeroLocus_empty_of_one_mem`：zeroLocus_empty_of_one_mem {s 
: Set R} (h : (1 : R) in s) : zeroLocus s = ∅
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem zeroLocus_univ : zeroLocus (Set.univ : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_univ 1)
/-
**PrimeSpectrum.vanishingIdeal_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：vanishingIdeal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s =
 ⊤ ↔ s = ∅
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal`：subset_zeroLocus_i
ff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) : t subseteq zero
Locus I ↔ I <= vanishingIdeal t
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `PrimeSpectrum.zeroLocus_univ`：zeroLocus_univ : zeroLocus (Set.univ : Set
 R) = ∅
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vanishingIdeal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s = ⊤ ↔ s = ∅ := by
  rw [← top_le_iff, ← subset_zeroLocus_iff_le_vanishingIdeal, Submodule.top_coe, zeroLocus_univ,
    Set.subset_empty_iff]
/-
**PrimeSpectrum.zeroLocus_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_eq_univ_iff (s : Set R) : zeroLocus s = Set.univ ↔ s subseteq ni
lradical R
参数：s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `PrimeSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal`：subset_zeroLoc
us_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) : t subsete
q zeroLocus s ↔ s subseteq vanishingIdeal t
· 使用定理 `PrimeSpectrum.vanishingIdeal_univ`：∀ {R : Type u} [inst : CommSemiring R
], PrimeSpectrum.vanishingIdeal Set.univ = nilradical R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zeroLocus_eq_univ_iff (s : Set R) :
    zeroLocus s = Set.univ ↔ s ⊆ nilradical R := by
  rw [← Set.univ_subset_iff, subset_zeroLocus_iff_subset_vanishingIdeal, vanishingIdeal_univ]
/-
**PrimeSpectrum.zeroLocus_sup** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_sup (I J : Ideal R) : zeroLocus ((I ⊔ J : Ideal R) : Set R) = ze
roLocus I inter zeroLocus J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem zeroLocus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I ∩ zeroLocus J :=
  (gc R).l_sup
/-
**PrimeSpectrum.zeroLocus_union** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_union (s s' : Set R) : zeroLocus (s union s') = zeroLocus s inte
r zeroLocus s'
参数：s s' : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem zeroLocus_union (s s' : Set R) : zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s' :=
  (gc_set R).l_sup
/-
**PrimeSpectrum.vanishingIdeal_union** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) : vanishingIdeal (t un
ion t') = vanishingIdeal t ⊓ vanishingIdeal t'
参数：t t' : Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf
/-
**PrimeSpectrum.zeroLocus_iSup** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_iSup {ι : Sort*} (I : ι -> Ideal R) : zeroLocus ((⨆ i, I i : Ide
al R) : Set R) = ⋂ i, zeroLocus (I i)
参数：I : ι -> Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem zeroLocus_iSup {ι : Sort*} (I : ι → Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_iSup
/-
**PrimeSpectrum.zeroLocus_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_iUnion {ι : Sort*} (s : ι -> Set R) : zeroLocus (⋃ i, s i) = ⋂ i
, zeroLocus (s i)
参数：s : ι -> Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem zeroLocus_iUnion {ι : Sort*} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_iSup
/-
**PrimeSpectrum.zeroLocus_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_iUnion {ι : Sort*} (s : ι -> Set R) : zeroLocus (⋃ i, s i) = ⋂ i
, zeroLocus (s i)
参数：s : ι -> Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `PrimeSpectrum.gc_set`：gc_set : @GaloisConnection (Set R) (Set (PrimeSpec
trum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t => vanishingIdeal t
-/
theorem zeroLocus_iUnion₂ {ι : Sort*} {κ : (i : ι) → Sort*} (s : ∀ i, κ i → Set R) :
    zeroLocus (⋃ (i) (j), s i j) = ⋂ (i) (j), zeroLocus (s i j) :=
  (gc_set R).l_iSup₂
/-
**PrimeSpectrum.zeroLocus_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_bUnion (s : Set (Set R)) : zeroLocus (⋃ s' in s, s' : Set R) = ⋂
 s' in s, zeroLocus s'
参数：s : Set (Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion`：zeroLocus_iUnion {ι : Sort*} (s : ι -> S
et R) : zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroLocus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, zeroLocus s' := by simp only [zeroLocus_iUnion]
/-
**PrimeSpectrum.vanishingIdeal_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：vanishingIdeal_iUnion {ι : Sort*} (t : ι -> Set (PrimeSpectrum R)) : vanis
hingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i)
参数：t : ι -> Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
-/
theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_iInf
/-
**PrimeSpectrum.zeroLocus_inf** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_inf (I J : Ideal R) : zeroLocus ((I ⊓ J : Ideal R) : Set R) = ze
roLocus I union zeroLocus J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsPrime.inf_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem zeroLocus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.inf_le
/-
**PrimeSpectrum.union_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：union_zeroLocus (s s' : Set R) : zeroLocus s union zeroLocus s' = zeroLocu
s (Ideal.span s ⊓ Ideal.span s' : Ideal R)
参数：s s' : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.zeroLocus_inf`：zeroLocus_inf (I J : Ideal R) : zeroLocus (
(I ⊓ J : Ideal R) : Set R) = zeroLocus I union zeroLocus J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_zeroLocus (s s' : Set R) :
    zeroLocus s ∪ zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) := by
  rw [zeroLocus_inf]
  simp
/-
**PrimeSpectrum.zeroLocus_mul** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_mul (I J : Ideal R) : zeroLocus ((I * J : Ideal R) : Set R) = ze
roLocus I union zeroLocus J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsPrime.mul_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I * J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem zeroLocus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.mul_le
/-
**PrimeSpectrum.zeroLocus_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：zeroLocus_singleton_mul (f g : R) : zeroLocus ({f * g} : Set R) = zeroLocu
s {f} union zeroLocus {g}
参数：f g : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsPrime.mul_mem_iff_mem_or_mem`：∀ {α : Type u} [inst : Semiring α]
 {I : Ideal α} [I.IsTwoSided], I.IsPrime → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ 
I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem zeroLocus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} ∪ zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]
/-
**PrimeSpectrum.zeroLocus_pow** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_pow (I : Ideal R) {n : Nat} (hn : n != 0) : zeroLocus ((I ^ n : 
Ideal R) : Set R) = zeroLocus I
参数：I : Ideal R；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.radical_pow`：∀ {R : Type u} [inst : CommSemiring R] (I : Ideal R) 
{n : ℕ}, n ≠ 0 → (I ^ n).radical = I.radical
-/
theorem zeroLocus_pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

@[simp]
/-
**PrimeSpectrum.zeroLocus_singleton_pow** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：zeroLocus_singleton_pow (f : R) (n : Nat) (hn : 0 < n) : zeroLocus ({f ^ n
} : Set R) = zeroLocus {f}
参数：f : R；n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem zeroLocus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn
/-
**PrimeSpectrum.sup_vanishingIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) : vanishingIdeal t ⊔ 
vanishingIdeal t' <= vanishingIdeal (t inter t')
参数：t t' : Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `PrimeSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (PrimeSpec
trum R)) (f : R) : f in vanishingIdeal t ↔ forall x in t, f in x.asIdeal
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [Submodule.mem_sup, mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim
/-
**PrimeSpectrum.mem_compl_zeroLocus_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：mem_compl_zeroLocus_iff_notMem {f : R} {I : PrimeSpectrum R} : I in (zeroL
ocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_compl_zeroLocus_iff_notMem {f : R} {I : PrimeSpectrum R} :
    I ∈ (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]
/-
**PrimeSpectrum.zeroLocus_insert_zero** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_insert_zero (s : Set R) : zeroLocus (insert 0 s) = zeroLocus s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `PrimeSpectrum.zeroLocus_union`：zeroLocus_union (s s' : Set R) : zeroLocu
s (s union s') = zeroLocus s inter zeroLocus s'
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_zero`：zeroLocus_singleton_zero : zeroL
ocus ({0} : Set R) = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
lemma zeroLocus_insert_zero (s : Set R) : zeroLocus (insert 0 s) = zeroLocus s := by
  rw [← Set.union_singleton, zeroLocus_union, zeroLocus_singleton_zero, Set.inter_univ]

@[simp]
/-
**PrimeSpectrum.zeroLocus_sdiff_singleton_zero** 是 Mathlib 中的一个引理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：zeroLocus_sdiff_singleton_zero (s : Set R) : zeroLocus (s \ {0}) = zeroLoc
us s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.zeroLocus_insert_zero`：zeroLocus_insert_zero (s : Set R) :
 zeroLocus (insert 0 s) = zeroLocus s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroLocus_sdiff_singleton_zero (s : Set R) : zeroLocus (s \ {0}) = zeroLocus s := by
  rw [← zeroLocus_insert_zero, ← zeroLocus_insert_zero (s := s)]; simp

@[deprecated (since := "2026-06-03")]
alias zeroLocus_diff_singleton_zero := zeroLocus_sdiff_singleton_zero
/-
**PrimeSpectrum.zeroLocus_smul_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：zeroLocus_smul_of_isUnit {r : R} (hr : IsUnit r) (s : Set R) : zeroLocus (
r • s) = zeroLocus s
参数：hr : IsUnit r；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.unit_mul_mem_iff_mem`：unit_mul_mem_iff_mem {x y : α} (hy : IsUnit 
y) : y * x in I ↔ x in I
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zeroLocus_smul_of_isUnit {r : R} (hr : IsUnit r) (s : Set R) :
    zeroLocus (r • s) = zeroLocus s := by
  ext; simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

section Order

/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] : OrderBot (PrimeSpectrum R) where
  bot := ⟨⊥, Ideal.isPrime_bot⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

@[simp]
/-
**PrimeSpectrum.asIdeal_bot** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：asIdeal_bot [IsDomain R] : (⊥ : PrimeSpectrum R).asIdeal = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem asIdeal_bot [IsDomain R] : (⊥ : PrimeSpectrum R).asIdeal = ⊥ := rfl
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Field R] : Unique (PrimeSpectrum R) where
  default := ⊥
  uniq x := PrimeSpectrum.ext ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right x.2.ne_top)

/-- Also see `PrimeSpectrum.isClosed_singleton_iff_isMaximal` -/
/-
**PrimeSpectrum.isMax_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isMax_iff {x : PrimeSpectrum R} : IsMax x ↔ x.asIdeal.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J

--- 原说明 ---
Also see `PrimeSpectrum.isClosed_singleton_iff_isMaximal`
-/
lemma isMax_iff {x : PrimeSpectrum R} :
    IsMax x ↔ x.asIdeal.IsMaximal := by
  refine ⟨fun hx ↦ ⟨⟨x.2.ne_top, fun I hI ↦ ?_⟩⟩, fun hx y e ↦ (hx.eq_of_le y.2.ne_top e).ge⟩
  by_contra e
  obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal I e
  exact hx.not_lt (show x < ⟨m, hm.isPrime⟩ from hI.trans_le hm')
/-
**PrimeSpectrum.zeroLocus_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：zeroLocus_eq_singleton (m : Ideal R) [m.IsMaximal] : zeroLocus m = {⟨m, in
ferInstance⟩}
参数：m : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
lemma zeroLocus_eq_singleton (m : Ideal R) [m.IsMaximal] :
    zeroLocus m = {⟨m, inferInstance⟩} := by
  ext I
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le ‹_› I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]
/-
**PrimeSpectrum.isMin_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isMin_iff {x : PrimeSpectrum R} : IsMin x ↔ x.asIdeal in minimalPrimes R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma isMin_iff {x : PrimeSpectrum R} :
    IsMin x ↔ x.asIdeal ∈ minimalPrimes R := by
  change IsMin _ ↔ Minimal (fun q : Ideal R ↦ q.IsPrime ∧ ⊥ ≤ q) _
  simp only [IsMin, Minimal, x.2, bot_le, and_self, and_true, true_and]
  exact ⟨fun H y hy e ↦ @H ⟨y, hy⟩ e, fun H y e ↦ H y.2 e⟩

end Order

section Noetherian

open Submodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- In a Noetherian ring, every ideal contains a product of prime ideals
([samuel1967, § 3.3, Lemma 3]). -/
/-
**PrimeSpectrum.exists_primeSpectrum_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：exists_primeSpectrum_prod_le (I : Ideal R) : exists Z : Multiset (PrimeSpe
ctrum R), Multiset.prod (Z.map asIdeal) <= I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.induction`：IsNoetherian.induction [IsNoetherian R M] {P : S
ubmodule R M -> Prop} (hgt : forall I, (forall J > I, P J) -> P I) (I : Submodul
e R M) : P I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Ideal.mem_sup_right`：mem_sup_right {S T : Ideal R} : forall {x : R}, x i
n T -> x in S ⊔ T
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.not_isPrime_iff`：not_isPrime_iff {I : Ideal α} : ¬I.IsPrime ↔ I = 
⊤ ∨ exists (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y in I
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.singleton_mul_singleton`：singleton_mul_singleton : ({a} : Set α) * {
b} = {a * b}
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
In a Noetherian ring, every ideal contains a product of prime ideals
([samuel1967, § 3.3, Lemma 3]).
-/
theorem exists_primeSpectrum_prod_le (I : Ideal R) :
    ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal R at M
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : ∀ z ∉ M, M < M + span R {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left htop
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  apply le_trans (mul_le_mul' h_Wx h_Wy)
  rw [add_mul]
  apply sup_le (show M * (M + span R {y}) ≤ M from Ideal.mul_le_left)
  rw [mul_add]
  apply sup_le (show span R {x} * M ≤ M from Ideal.mul_le_right)
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]

/-- In a Noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel1967, § 3.3, Lemma 3]) -/
/-
**PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain** 是 Mathlib 中的
一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I :
 Ideal A} (h_nzI : I != ⊥) : exists Z : Multiset (PrimeSpectrum A), Multiset.pro
d (Z.map asIdeal) <= I ∧ Multiset.prod (Z.map asIdeal) != ⊥
参数：h_fA : ¬IsField A；h_nzI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.induction`：IsNoetherian.induction [IsNoetherian R M] {P : S
ubmodule R M -> Prop} (hgt : forall I, (forall J > I, P J) -> P I) (I : Submodul
e R M) : P I
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.not_isField_iff_exists_prime`：not_isField_iff_exists_prime [Nontriv
ial R] : ¬IsField R ↔ exists p : Ideal R, p != ⊥ ∧ p.IsPrime
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.not_isPrime_iff`：not_isPrime_iff {I : Ideal α} : ¬I.IsPrime ↔ I = 
⊤ ∨ exists (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y in I
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
In a Noetherian integral domain which is not a field, every non-zero ideal conta
ins a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal contai
ning only 0 as
  product or prime ideals ([samuel1967, § 3.3, Lemma 3])
-/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥ := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal A at M
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime := by
      apply Ring.not_isField_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h_prM : M.IsPrime
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    exact ⟨le_rfl, h_nzI⟩
  obtain ⟨x, hx, y, hy, h_xy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left h_topM
  have lt_add : ∀ z ∉ M, M < M + span A {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  refine ⟨le_trans (mul_le_mul' h_Wx_le h_Wy_le) ?_, mt Ideal.mul_eq_bot.mp ?_⟩
  · rw [add_mul]
    apply sup_le (show M * (M + span A {y}) ≤ M from Ideal.mul_le_left)
    rw [mul_add]
    apply sup_le (show span A {x} * M ≤ M from Ideal.mul_le_right)
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  · rintro (hx | hy) <;> contradiction

end Noetherian

end CommSemiRing

end PrimeSpectrum

