/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.JacobsonSpace

/-!
# The prime spectrum of a Jacobson ring

## Main results
- `PrimeSpectrum.exists_isClosed_singleton_of_isJacobson`:
  The spectrum of a Jacobson ring is a Jacobson space.
- `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobson`:
  If `R` is both Noetherian and Jacobson, then the following are equivalent for `x : Spec R`:
  1. `{x}` is open (i.e. `x` is an isolated point)
  2. `{x}` is clopen
  3. `{x}` is both closed and stable under generalization
    (i.e. `x` is both a minimal prime and a maximal ideal)
-/

public section

open Ideal

variable {R : Type*} [CommRing R]

namespace PrimeSpectrum

/-
**PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing** 是 Mathlib 中的一个引理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：exists_isClosed_singleton_of_isJacobsonRing [IsJacobsonRing R] (s : (Set (
PrimeSpectrum R))) (hs : IsOpen s) (hs' : s.Nonempty) : exists x in s, IsClosed 
{x}
参数：s : (Set (PrimeSpectrum R))；hs : IsOpen s；hs' : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`：isClosed_iff_zeroLocus_ideal
 (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_compl_comm`：eq_compl_comm : x = yᶜ ↔ y = xᶜ
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PrimeSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : 
Set R) = Set.univ
· 使用定理 `PrimeSpectrum.zeroLocus_eq_iff`：zeroLocus_eq_iff {I J : Ideal R} : zeroL
ocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical
· 使用定理 `Ideal.radical_eq_jacobson`：Ideal.radical_eq_jacobson [H : IsJacobsonRing
 R] (I : Ideal R) : I.radical = I.jacobson
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.jacobson_mono`：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobso
n <= J.jacobson
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma exists_isClosed_singleton_of_isJacobsonRing [IsJacobsonRing R]
    (s : (Set (PrimeSpectrum R))) (hs : IsOpen s) (hs' : s.Nonempty) :
    ∃ x ∈ s, IsClosed {x} := by
  simp_rw [isClosed_singleton_iff_isMaximal]
  obtain ⟨I, hI'⟩ := (isClosed_iff_zeroLocus_ideal _).mp hs.isClosed_compl
  simp_rw [← @Set.notMem_compl_iff _ s, hI', mem_zeroLocus]
  have := hs'.ne_empty
  contrapose! this
  simp_rw [not_imp_not] at this
  rw [← Set.compl_univ, eq_compl_comm, hI', eq_comm, ← zeroLocus_bot,
    zeroLocus_eq_iff, Ideal.radical_eq_jacobson, Ideal.radical_eq_jacobson]
  refine le_antisymm (le_sInf ?_) (Ideal.jacobson_mono bot_le)
  rintro x ⟨-, hx⟩
  exact sInf_le ⟨this ⟨x, hx.isPrime⟩ hx, hx⟩
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsJacobsonRing R] : JacobsonSpace (PrimeSpectrum R) := by
  rw [jacobsonSpace_iff_locallyClosed]
  rintro S hS ⟨U, Z, hU, hZ, rfl⟩
  simp only [← isClosed_compl_iff, isClosed_iff_zeroLocus_ideal, @compl_eq_comm _ U] at hU hZ
  obtain ⟨⟨I, rfl⟩, ⟨J, rfl⟩⟩ := And.intro hU hZ
  simp only [Set.nonempty_iff_ne_empty, ne_eq, Set.inter_assoc,
    ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset,
    zeroLocus_subset_zeroLocus_iff, Ideal.radical_eq_jacobson, Ideal.jacobson, le_sInf_iff] at hS ⊢
  contrapose hS
  rintro x ⟨hJx, hx⟩
  exact @hS ⟨x, hx.isPrime⟩ ⟨hJx, (isClosed_singleton_iff_isMaximal _).mpr hx⟩
/-
**PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：isJacobsonRing_iff_jacobsonSpace : IsJacobsonRing R ↔ JacobsonSpace (Prime
Spectrum R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.instJacobsonSpaceOfIsJacobsonRing`：∀ {R : Type u_1} [inst 
: CommRing R] [IsJacobsonRing R], JacobsonSpace (PrimeSpectrum R)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsRadical.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsRadical → I.radical = I
· 使用引理 `Ideal.isRadical_jacobson`：isRadical_jacobson (I : Ideal R) : I.jacobson.
IsRadical
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PrimeSpectrum.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {s t : 
Set (PrimeSpectrum R)} (h : s subseteq t) : vanishingIdeal t <= vanishingIdeal s
· 使用定理 `JacobsonSpace.closure_inter_closedPoints`：∀ {X : Type u_1} {inst : Topol
ogicalSpace X} [self : JacobsonSpace X] {Z : Set X},   IsClosed Z → closure (Z ∩
 closedPoints X) = Z
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
lemma isJacobsonRing_iff_jacobsonSpace :
    IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R) := by
  refine ⟨fun _ ↦ inferInstance, fun H ↦ ⟨fun I hI ↦ le_antisymm ?_ Ideal.le_jacobson⟩⟩
  rw [← I.isRadical_jacobson.radical]
  conv_rhs => rw [← hI.radical]
  simp_rw [← vanishingIdeal_zeroLocus_eq_radical]
  apply vanishingIdeal_anti_mono
  rw [← H.1 (isClosed_zeroLocus I), (isClosed_zeroLocus _).closure_subset_iff]
  rintro x ⟨hx : I ≤ x.asIdeal, hx'⟩
  change jacobson I ≤ x.asIdeal
  exact sInf_le ⟨hx, (isClosed_singleton_iff_isMaximal _).mp hx'⟩

/--
If `R` is both Noetherian and Jacobson, then the following are equivalent for `x : Spec R`:
1. `{x}` is open (i.e. `x` is an isolated point)
2. `{x}` is clopen
3. `{x}` is both closed and stable under generalization
  (i.e. `x` is both a minimal prime and a maximal ideal)
-/
/-
**PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing** 是 Math
lib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing [IsNoetherianRing 
R] [IsJacobsonRing R] (x : PrimeSpectrum R) : List.TFAE [IsOpen {x}, IsClopen {x
}, IsClosed {x} ∧ StableUnderGeneralization {x}]
参数：x : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing`：exists_isClos
ed_singleton_of_isJacobsonRing [IsJacobsonRing R] (s : (Set (PrimeSpectrum R))) 
(hs : IsOpen s) (hs' : s.Nonempty) : exists x i…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsMin.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMi
n a → b ≤ a → b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.isMin_iff`：isMin_iff {x : PrimeSpectrum R} : IsMin x ↔ x.a
sIdeal in minimalPrimes R
· 使用引理 `PrimeSpectrum.stableUnderGeneralization_singleton`：stableUnderGeneraliza
tion_singleton {x : PrimeSpectrum R} : StableUnderGeneralization {x} ↔ x.asIdeal
 in minimalPrimes R
· 使用引理 `PrimeSpectrum.isMax_iff`：isMax_iff {x : PrimeSpectrum R} : IsMax x ↔ x.a
sIdeal.IsMaximal
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `IsMax.eq_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → b = a
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` is both Noetherian and Jacobson, then the following are equivalent for `x
 : Spec R`:
1. `{x}` is open (i.e. `x` is an isolated point)
2. `{x}` is clopen
3. `{x}` is both closed and stable under generalization
  (i.e. `x` is both a minimal prime and a maximal ideal)
-/
lemma isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
    [IsNoetherianRing R] [IsJacobsonRing R] (x : PrimeSpectrum R) :
    List.TFAE [IsOpen {x}, IsClopen {x}, IsClosed {x} ∧ StableUnderGeneralization {x}] := by
  tfae_have 1 → 2
  | h => by
    obtain ⟨y, rfl : y = x, h'⟩ := exists_isClosed_singleton_of_isJacobsonRing _ h
      ⟨x, Set.mem_singleton x⟩
    exact ⟨h', h⟩
  tfae_have 2 → 3
  | h => ⟨h.isClosed, h.isOpen.stableUnderGeneralization⟩
  tfae_have 3 → 1
  | ⟨h₁, h₂⟩ => by
    rw [isClosed_singleton_iff_isMaximal, ← isMax_iff] at h₁
    suffices {x} = (⋃ p ∈ { p : PrimeSpectrum R | IsMin p ∧ p ≠ x }, closure {p})ᶜ by
      rw [this, isOpen_compl_iff]
      refine Set.Finite.isClosed_biUnion ?_ (fun _ _ ↦ isClosed_closure)
      exact (finite_setOfPred_isMin R).subset fun x h ↦ h.1
    ext p
    simp only [Set.mem_singleton_iff, ne_eq, Set.mem_ofPred_eq, Set.compl_iUnion, Set.mem_iInter,
      Set.mem_compl_iff, and_imp, ← specializes_iff_mem_closure, ← le_iff_specializes,
      not_imp_not]
    constructor
    · rintro rfl _ _
      rw [stableUnderGeneralization_singleton, ← isMin_iff] at h₂
      exact h₂.eq_of_le
    · intro hp
      apply h₁.eq_of_ge
      obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
      exact (hp ⟨q, hq.1.1⟩ (isMin_iff.mpr hq) hq').ge.trans hq'
  tfae_finish

end PrimeSpectrum

