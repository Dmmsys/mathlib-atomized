/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Nullstellensatz

This file establishes a version of Hilbert's classical Nullstellensatz for `MvPolynomial`s.
The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.

The statement is in terms of new definitions `vanishingIdeal` and `zeroLocus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishingIdeal` and `zeroLocus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

@[expose] public section

open Ideal

noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*}

variable (K) in
/-- Set of points that are zeroes of all polynomials in an ideal -/
/-
**MvPolynomial.zeroLocus** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ -> K)
参数：I : Ideal (MvPolynomial σ k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Set of points that are zeroes of all polynomials in an ideal
-/
def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → K) :=
  {x : σ → K | ∀ p ∈ I, aeval x p = 0}

@[simp]
/-
**MvPolynomial.mem_zeroLocus_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_zeroLocus_iff {I : Ideal (MvPolynomial σ k)} {x : σ -> K} : x in zeroL
ocus K I ↔ forall p in I, aeval x p = 0
参数：MvPolynomial σ k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_zeroLocus_iff {I : Ideal (MvPolynomial σ k)} {x : σ → K} :
    x ∈ zeroLocus K I ↔ ∀ p ∈ I, aeval x p = 0 :=
  Iff.rfl
/-
**MvPolynomial.zeroLocus_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：zeroLocus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I <= J) : zeroLo
cus K J <= zeroLocus K I
参数：MvPolynomial σ k；h : I <= J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroLocus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) :
    zeroLocus K J ≤ zeroLocus K I := fun _ hx p hp => hx p <| h hp

@[simp]
/-
**MvPolynomial.zeroLocus_bot** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：zeroLocus_bot : zeroLocus K (⊥ : Ideal (MvPolynomial σ k)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem zeroLocus_bot : zeroLocus K (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x _ _ hp => Trans.trans (congr_arg (aeval x) (mem_bot.1 hp)) (eval x).map_zero

@[simp]
/-
**MvPolynomial.zeroLocus_top** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：zeroLocus_top : zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem zeroLocus_top : zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2 fun x hx => one_ne_zero
    ((aeval (R := k) x).map_one ▸ hx 1 Submodule.mem_top : (1 : K) = 0)

variable (k) in
/-- Ideal of polynomials with common zeroes at all elements of a set -/
/-
**MvPolynomial.vanishingIdeal** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：vanishingIdeal (V : Set (σ -> K)) : Ideal (MvPolynomial σ k) where carrier
参数：V : Set (σ -> K)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ideal of polynomials with common zeroes at all elements of a set
-/
def vanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) where
  carrier := {p | ∀ x ∈ V, aeval x p = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, map_add]
  smul_mem' p q hq x hx := by
    simp only [hq x hx, smul_eq_mul, mul_zero, map_mul]

@[simp]
/-
**MvPolynomial.mem_vanishingIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_vanishingIdeal_iff {V : Set (σ -> K)} {p : MvPolynomial σ k} : p in va
nishingIdeal k V ↔ forall x in V, aeval x p = 0
参数：σ -> K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vanishingIdeal_iff {V : Set (σ → K)} {p : MvPolynomial σ k} :
    p ∈ vanishingIdeal k V ↔ ∀ x ∈ V, aeval x p = 0 :=
  Iff.rfl
/-
**MvPolynomial.vanishingIdeal_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：vanishingIdeal_anti_mono {A B : Set (σ -> K)} (h : A <= B) : vanishingIdea
l k B <= vanishingIdeal k A
参数：σ -> K；h : A <= B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vanishingIdeal_anti_mono {A B : Set (σ → K)} (h : A ≤ B) :
    vanishingIdeal k B ≤ vanishingIdeal k A := fun _ hp x hx => hp x <| h hx
/-
**MvPolynomial.vanishingIdeal_empty** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ -> K)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ → K)) = ⊤ :=
  le_antisymm le_top fun _ _ x hx => absurd hx (Set.notMem_empty x)
/-
**MvPolynomial.le_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) : I <= vanishin
gIdeal k (zeroLocus K I)
参数：I : Ideal (MvPolynomial σ k)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I ≤ vanishingIdeal k (zeroLocus K I) := fun p hp _ hx => hx p hp
/-
**MvPolynomial.zeroLocus_vanishingIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：zeroLocus_vanishingIdeal_le (V : Set (σ -> K)) : V <= zeroLocus K (vanishi
ngIdeal k V)
参数：V : Set (σ -> K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroLocus_vanishingIdeal_le (V : Set (σ → K)) : V ≤ zeroLocus K (vanishingIdeal k V) :=
  fun V hV _ hp => hp V hV
/-
**MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：zeroLocus_vanishingIdeal_galoisConnection : @GaloisConnection (Ideal (MvPo
lynomial σ k)) (Set (σ -> K))ᵒᵈ _ _ (zeroLocus K) (vanishingIdeal k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_intro`：monotone_intro (hu : Monotone u) (hl : 
Monotone l) (h_u_l : forall a, a <= u (l a)) (h_l_u : forall a, l (u a) <= a) : 
GaloisConnection l u
· 使用定理 `MvPolynomial.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {A B : S
et (σ -> K)} (h : A <= B) : vanishingIdeal k B <= vanishingIdeal k A
· 使用定理 `MvPolynomial.zeroLocus_anti_mono`：zeroLocus_anti_mono {I J : Ideal (MvPo
lynomial σ k)} (h : I <= J) : zeroLocus K J <= zeroLocus K I
· 使用定理 `MvPolynomial.le_vanishingIdeal_zeroLocus`：le_vanishingIdeal_zeroLocus (I
 : Ideal (MvPolynomial σ k)) : I <= vanishingIdeal k (zeroLocus K I)
· 使用定理 `MvPolynomial.zeroLocus_vanishingIdeal_le`：zeroLocus_vanishingIdeal_le (V
 : Set (σ -> K)) : V <= zeroLocus K (vanishingIdeal k V)
-/
theorem zeroLocus_vanishingIdeal_galoisConnection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → K))ᵒᵈ _ _
      (zeroLocus K) (vanishingIdeal k) :=
  GaloisConnection.monotone_intro (fun _ _ ↦ vanishingIdeal_anti_mono)
    (fun _ _ ↦ zeroLocus_anti_mono) le_vanishingIdeal_zeroLocus zeroLocus_vanishingIdeal_le
/-
**MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：le_zeroLocus_iff_le_vanishingIdeal {V : Set (σ -> K)} {I : Ideal (MvPolyno
mial σ k)} : V <= zeroLocus K I ↔ I <= vanishingIdeal k V
参数：σ -> K；MvPolynomial σ k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`：zeroLocus_vanish
ingIdeal_galoisConnection : @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ
 -> K))ᵒᵈ _ _ (zeroLocus K) (vanishingIdeal …
-/
theorem le_zeroLocus_iff_le_vanishingIdeal {V : Set (σ → K)} {I : Ideal (MvPolynomial σ k)} :
    V ≤ zeroLocus K I ↔ I ≤ vanishingIdeal k V :=
  zeroLocus_vanishingIdeal_galoisConnection.le_iff_le
/-
**MvPolynomial.zeroLocus_span** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：zeroLocus_span (S : Set (MvPolynomial σ k)) : zeroLocus K (Ideal.span S) =
 { x | forall p in S, aeval x p = 0 }
参数：S : Set (MvPolynomial σ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal`：le_zeroLocus_iff_le_van
ishingIdeal {V : Set (σ -> K)} {I : Ideal (MvPolynomial σ k)} : V <= zeroLocus K
 I ↔ I <= vanishingIdeal k V
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem zeroLocus_span (S : Set (MvPolynomial σ k)) :
    zeroLocus K (Ideal.span S) = { x | ∀ p ∈ S, aeval x p = 0 } :=
  eq_of_forall_le_iff fun _ => le_zeroLocus_iff_le_vanishingIdeal.trans <|
    Ideal.span_le.trans forall₂_comm
/-
**MvPolynomial.mem_vanishingIdeal_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：mem_vanishingIdeal_singleton_iff (x : σ -> K) (p : MvPolynomial σ k) : p i
n (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) ↔ aeval x p = 0
参数：x : σ -> K；p : MvPolynomial σ k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_vanishingIdeal_singleton_iff (x : σ → K) (p : MvPolynomial σ k) :
    p ∈ (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) ↔ aeval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx _ hy => hy.symm ▸ hpx⟩
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : σ → K} : (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)).IsPrime := by
  convert! RingHom.ker_isPrime (aeval (R := k) x)
  ext; simp
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : σ → K} : (vanishingIdeal K {x} : Ideal (MvPolynomial σ K)).IsMaximal := by
  convert! RingHom.ker_isMaximal_of_surjective (aeval (R := K) x) ?_
  · ext; simp
  · intro z; use C z; simp
/-
**MvPolynomial.radical_le_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) : I.rad
ical <= vanishingIdeal k (zeroLocus K I)
参数：I : Ideal (MvPolynomial σ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_vanishingIdeal_singleton_iff`：mem_vanishingIdeal_single
ton_iff (x : σ -> K) (p : MvPolynomial σ k) : p in (vanishingIdeal k {x} : Ideal
 (MvPolynomial σ k)) ↔ aeval x p = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MvPolynomial.le_vanishingIdeal_zeroLocus`：le_vanishingIdeal_zeroLocus (I
 : Ideal (MvPolynomial σ k)) : I <= vanishingIdeal k (zeroLocus K I)
· 使用定理 `MvPolynomial.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {A B : S
et (σ -> K)} (h : A <= B) : vanishingIdeal k B <= vanishingIdeal k A
· 使用定理 `MvPolynomial.instIsPrimeVanishingIdealSingletonForallSet`：∀ {k : Type u_
1} {K : Type u_2} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {σ 
: Type u_3} {x : σ → K},   (MvPolynomial.vanis…
-/
theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I.radical ≤ vanishingIdeal k (zeroLocus K I) := by
  intro p hp x hx
  rw [← mem_vanishingIdeal_singleton_iff]
  rw [radical_eq_sInf] at hp
  refine
    (mem_sInf.mp hp)
      ⟨le_trans (le_vanishingIdeal_zeroLocus I)
          (vanishingIdeal_anti_mono fun y hy => hy.symm ▸ hx),
        inferInstance⟩

/-- The point in the prime spectrum associated to a given point -/
/-
**MvPolynomial.pointToPoint** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：pointToPoint (x : σ -> K) : PrimeSpectrum (MvPolynomial σ k)
参数：x : σ -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point in the prime spectrum associated to a given point
-/
def pointToPoint (x : σ → K) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩

@[simp]
/-
**MvPolynomial.vanishingIdeal_pointToPoint** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：vanishingIdeal_pointToPoint (V : Set (σ -> K)) : PrimeSpectrum.vanishingId
eal (pointToPoint '' V) = MvPolynomial.vanishingIdeal k V
参数：V : Set (σ -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (PrimeSpec
trum R)) (f : R) : f in vanishingIdeal t ↔ forall x in t, f in x.asIdeal
· 使用定理 `MvPolynomial.instIsPrimeVanishingIdealSingletonForallSet`：∀ {k : Type u_
1} {K : Type u_2} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {σ 
: Type u_3} {x : σ → K},   (MvPolynomial.vanis…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem vanishingIdeal_pointToPoint (V : Set (σ → K)) :
    PrimeSpectrum.vanishingIdeal (pointToPoint '' V) = MvPolynomial.vanishingIdeal k V :=
  le_antisymm
    (fun _ hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
        (⟨x, hx, rfl⟩ : _))
        x rfl)
    fun _ hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun _ hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun _ hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1
/-
**MvPolynomial.pointToPoint_zeroLocus_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：pointToPoint_zeroLocus_le (I : Ideal (MvPolynomial σ K)) : pointToPoint (k
参数：I : Ideal (MvPolynomial σ K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MvPolynomial.le_vanishingIdeal_zeroLocus`：le_vanishingIdeal_zeroLocus (I
 : Ideal (MvPolynomial σ k)) : I <= vanishingIdeal k (zeroLocus K I)
· 使用定理 `MvPolynomial.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {A B : S
et (σ -> K)} (h : A <= B) : vanishingIdeal k B <= vanishingIdeal k A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pointToPoint_zeroLocus_le (I : Ideal (MvPolynomial σ K)) :
    pointToPoint (k := K) '' MvPolynomial.zeroLocus K I ≤ PrimeSpectrum.zeroLocus I := fun J hJ =>
  let ⟨_, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus (K := K) I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I ≤ J.asIdeal)

variable [IsAlgClosed K] [Finite σ]

variable (K) in
/-
**MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：eq_vanishingIdeal_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (h
I : I.IsMaximal) : exists x : σ -> K, I = vanishingIdeal k {x}
参数：MvPolynomial σ k；hI : I.IsMaximal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.isAlgebraic_iff_isIntegral`：∀ {K : Type u} {A : Type v} [inst : 
Field K] [inst_1 : Ring A] [inst_2 : Algebra K A],   Algebra.IsAlgebraic K A ↔ A
lgebra.IsIntegral K A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `algebraMap_isIntegral_iff`：algebraMap_isIntegral_iff : (algebraMap R A).
IsIntegral ↔ Algebra.IsIntegral R A
· 使用定理 `MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing`：comp_C_int
egral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R
] {σ : Type*} [Finite σ] {S : Type*} [Field S] (f …
· 使用定理 `instIsJacobsonRingOfIsArtinianRing`：∀ {R : Type u_1} [inst : CommRing R]
 [IsArtinianRing R], IsJacobsonRing R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eq_vanishingIdeal_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) :
    ∃ x : σ → K, I = vanishingIdeal k {x} := by
  let : Field (MvPolynomial σ k ⧸ I) := Quotient.field I
  have : Algebra.IsAlgebraic k (MvPolynomial σ k ⧸ I) := by
    rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : (MvPolynomial σ k ⧸ I) →ₐ[k] K := IsAlgClosed.lift
  let x : σ → K := fun s => φ (Ideal.Quotient.mk I (X s))
  have : aeval x = φ.comp (Quotient.mkₐ k I) := by ext; simp [x]
  use x
  simp [Ideal.ext_iff, this, Ideal.Quotient.eq_zero_iff_mem]
/-
**MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：isMaximal_iff_eq_vanishingIdeal_singleton {I : Ideal (MvPolynomial σ K)} :
 I.IsMaximal ↔ exists x : σ -> K, I = vanishingIdeal K {x}
参数：MvPolynomial σ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`：eq_vanishingIdeal
_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) : exis
ts x : σ -> K, I = vanishingIdeal k {x}
· 使用定理 `MvPolynomial.instIsMaximalVanishingIdealSingletonForallSet`：∀ {K : Type 
u_2} [inst : Field K] {σ : Type u_3} {x : σ → K}, (MvPolynomial.vanishingIdeal K
 {x}).IsMaximal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMaximal_iff_eq_vanishingIdeal_singleton {I : Ideal (MvPolynomial σ K)} :
    I.IsMaximal ↔ ∃ x : σ → K, I = vanishingIdeal K {x} :=
  ⟨eq_vanishingIdeal_singleton_of_isMaximal K,
    fun ⟨_, hx⟩ => hx ▸ inferInstance⟩

/-- Main statement of the Nullstellensatz -/
@[simp]
/-
**MvPolynomial.vanishingIdeal_zeroLocus_eq_radical** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) : vanis
hingIdeal k (zeroLocus K I) = I.radical
参数：I : Ideal (MvPolynomial σ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_jacobson`：Ideal.radical_eq_jacobson [H : IsJacobsonRing
 R] (I : Ideal R) : I.radical = I.jacobson
· 使用定理 `instIsJacobsonRingOfIsArtinianRing`：∀ {R : Type u_1} [inst : CommRing R]
 [IsArtinianRing R], IsJacobsonRing R
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`：eq_vanishingIdeal
_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) : exis
ts x : σ -> K, I = vanishingIdeal k {x}
· 使用定理 `MvPolynomial.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {A B : S
et (σ -> K)} (h : A <= B) : vanishingIdeal k B <= vanishingIdeal k A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_vanishingIdeal_singleton_iff`：mem_vanishingIdeal_single
ton_iff (x : σ -> K) (p : MvPolynomial σ k) : p in (vanishingIdeal k {x} : Ideal
 (MvPolynomial σ k)) ↔ aeval x p = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `MvPolynomial.radical_le_vanishingIdeal_zeroLocus`：radical_le_vanishingId
eal_zeroLocus (I : Ideal (MvPolynomial σ k)) : I.radical <= vanishingIdeal k (ze
roLocus K I)

--- 原说明 ---
Main statement of the Nullstellensatz
-/
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal k (zeroLocus K I) = I.radical := by
  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
  rw [I.radical_eq_jacobson]
  apply le_sInf
  rintro J ⟨hJI, hJ⟩
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine hx.symm ▸ vanishingIdeal_anti_mono fun y hy p hp => ?_
  rw [← mem_vanishingIdeal_singleton_iff, Set.mem_singleton_iff.1 hy, ← hx]
  exact hJI hp

@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`
/-
**MvPolynomial.IsPrime.vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial.IsPrime`。
形式化陈述：∀ {k : Type u_1} {K : Type u_2} [inst : Field k] [inst_1 : Field K] [inst_
2 : Algebra k K] {σ : Type u_3}   [IsAlgClosed K] [Finite σ] (P : Ideal (MvPolyn
omial σ k)) [h : P.IsPrime],   MvPolynomial.vanishingIdeal k (MvPolynomial.zeroL
ocus K P) = P
参数：P : Ideal (MvPolynomial σ k)；MvPolynomial.zeroLocus K P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLoc
us_eq_radical (I : Ideal (MvPolynomial σ k)) : vanishingIdeal k (zeroLocus K I) 
= I.radical
· 使用定理 `Ideal.IsPrime.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ideal
 R}, I.IsPrime → I.radical = I
-/
theorem IsPrime.vanishingIdeal_zeroLocus (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime] :
    vanishingIdeal k (zeroLocus K P) = P :=
  Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical

end MvPolynomial

