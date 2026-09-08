/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!

# Maximal ideal of local rings

We prove basic properties of the maximal ideal of a local ring.

-/

public section

namespace IsLocalRing

variable {R S K : Type*}

section CommSemiring

variable [CommSemiring R] [IsLocalRing R]

@[simp]
/-
**IsLocalRing.mem_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：mem_maximalIdeal (x) : x in maximalIdeal R ↔ x in nonunits R
参数：x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_maximalIdeal (x) : x ∈ maximalIdeal R ↔ x ∈ nonunits R :=
  Iff.rfl

variable (R)
/-
**IsLocalRing.maximalIdeal.isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.maxi
malIdeal`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : IsLocalRing R], (IsLoca
lRing.maximalIdeal R).IsMaximal
参数：R : Type u_1；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
instance maximalIdeal.isMaximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    rw [mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H
/-
**IsLocalRing.isMaximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I = maximalIdeal R where mp hI
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I = maximalIdeal R where
  mp hI := hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ h ↦ hI.1.1 ∘ I.eq_top_of_isUnit_mem h
  mpr e := e ▸ maximalIdeal.isMaximal R
/-
**IsLocalRing.maximal_ideal_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：maximal_ideal_unique : exists! I : Ideal R, I.IsMaximal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem maximal_ideal_unique : ∃! I : Ideal R, I.IsMaximal := by
  simp [isMaximal_iff]

variable {R}
/-
**IsLocalRing.eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R
参数：hI : I.IsMaximal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `IsLocalRing.maximal_ideal_unique`：maximal_ideal_unique : exists! I : Ide
al R, I.IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
  ExistsUnique.unique (maximal_ideal_unique R) hI <| maximalIdeal.isMaximal R

/-- The maximal spectrum of a local ring is a singleton. -/
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal spectrum of a local ring is a singleton.
-/
instance : Unique (MaximalSpectrum R) where
  default := ⟨maximalIdeal R, maximalIdeal.isMaximal R⟩
  uniq := fun I ↦ MaximalSpectrum.ext_iff.mpr <| eq_maximalIdeal I.isMaximal

omit [IsLocalRing R] in
/-- If the maximal spectrum of a ring is a singleton, then the ring is local. -/
/-
**IsLocalRing.of_singleton_maximalSpectrum** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRin
g`。
形式化陈述：of_singleton_maximalSpectrum [Subsingleton (MaximalSpectrum R)] [Nonempty 
(MaximalSpectrum R)] : IsLocalRing R
参数：MaximalSpectrum R；MaximalSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_unique_max_ideal`：of_unique_max_ideal (h : exists! I : Id
eal R, I.IsMaximal) : IsLocalRing R
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `MaximalSpectrum.mk.inj`：∀ {R : Type u_1} {inst : CommSemiring R} {asIdea
l : Ideal R} {isMaximal : asIdeal.IsMaximal} {asIdeal_1 : Ideal R}   {isMaximal_
1 : asIdeal_…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If the maximal spectrum of a ring is a singleton, then the ring is local.
-/
theorem of_singleton_maximalSpectrum [Subsingleton (MaximalSpectrum R)]
    [Nonempty (MaximalSpectrum R)] : IsLocalRing R :=
  let m := Classical.arbitrary (MaximalSpectrum R)
  .of_unique_max_ideal ⟨m.asIdeal, m.isMaximal,
    fun I hI ↦ MaximalSpectrum.mk.inj <| Subsingleton.elim ⟨I, hI⟩ m⟩
/-
**IsLocalRing.le_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤) : J <= maximalIdeal R
参数：hJ : J != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
-/
theorem le_maximalIdeal {J : Ideal R} (hJ : J ≠ ⊤) : J ≤ maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]
/-
**IsLocalRing.le_maximalIdeal_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`
。
形式化陈述：le_maximalIdeal_of_isPrime (p : Ideal R) [hp : p.IsPrime] : p <= maximalId
eal R
参数：p : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem le_maximalIdeal_of_isPrime (p : Ideal R) [hp : p.IsPrime] : p ≤ maximalIdeal R :=
  le_maximalIdeal hp.ne_top

/--
An element `x` of a commutative local semiring is not contained in the maximal ideal
iff it is a unit.
-/
/-
**IsLocalRing.notMem_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：notMem_maximalIdeal {x : R} : x ∉ maximalIdeal R ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element `x` of a commutative local semiring is not contained in the maximal i
deal
iff it is a unit.
-/
theorem notMem_maximalIdeal {x : R} : x ∉ maximalIdeal R ↔ IsUnit x := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
/-
**IsLocalRing.isField_iff_maximalIdeal_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing
`。
形式化陈述：isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ring.not_isField_iff_exists_prime`：not_isField_iff_exists_prime [Nontriv
ial R] : ¬IsField R ↔ exists p : Ideal R, p != ⊥ ∧ p.IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
-/
theorem isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥ :=
  not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩

end CommSemiring

section CommRing

variable [CommRing R] [IsLocalRing R]

/-
**IsLocalRing.maximalIdeal_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：maximalIdeal_le_jacobson (I : Ideal R) : IsLocalRing.maximalIdeal R <= I.j
acobson
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
-/
theorem maximalIdeal_le_jacobson (I : Ideal R) :
    IsLocalRing.maximalIdeal R ≤ I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm
/-
**IsLocalRing.jacobson_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：jacobson_eq_maximalIdeal (I : Ideal R) (h : I != ⊤) : I.jacobson = IsLocal
Ring.maximalIdeal R
参数：I : Ideal R；h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
-/
theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I ≠ ⊤) :
    I.jacobson = IsLocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

variable (R) in
/-
**IsLocalRing.ringJacobson_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRin
g`。
形式化陈述：ringJacobson_eq_maximalIdeal : Ring.jacobson R = maximalIdeal R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.jacobson_bot`：jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobso
n R
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
-/
theorem ringJacobson_eq_maximalIdeal : Ring.jacobson R = maximalIdeal R :=
  Ideal.jacobson_bot.symm.trans (jacobson_eq_maximalIdeal _ top_ne_bot.symm)

end CommRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
**IsLocalRing.ker_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：ker_eq_maximalIdeal [DivisionRing K] (φ : R ->+* K) (hφ : Function.Surject
ive φ) : RingHom.ker φ = maximalIdeal R
参数：φ : R ->+* K；hφ : Function.Surjective φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `RingHom.ker_isMaximal_of_surjective`：ker_isMaximal_of_surjective {R K F 
: Type*} [Ring R] [DivisionRing K] [FunLike F R K] [RingHomClass F R K] (f : F) 
(hf : Function.Surjective…
-/
theorem ker_eq_maximalIdeal [DivisionRing K] (φ : R →+* K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal <| (RingHom.ker_isMaximal_of_surjective φ) hφ

end

/-
**IsLocalRing.maximalIdeal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：maximalIdeal_eq_bot {R : Type*} [Field R] : IsLocalRing.maximalIdeal R = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
-/
theorem maximalIdeal_eq_bot {R : Type*} [Field R] : IsLocalRing.maximalIdeal R = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)

end IsLocalRing

/-
**Subsemiring.isLocalRing_of_unit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsemiring.isLocalRing_of_unit {R : Type*} [Semiring R] [IsLocalRing R] (
S : Subsemiring R) (h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (⟨
x, hx⟩ : S)) : IsLocalRing S where isUnit_or_isUnit_of_add_one {x y} hxy
参数：S : Subsemiring R；h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (
⟨x, hx⟩ : S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma Subsemiring.isLocalRing_of_unit {R : Type*} [Semiring R] [IsLocalRing R] (S : Subsemiring R)
    (h_unit : ∀ (x : R) (hx : x ∈ S), IsUnit x → IsUnit (⟨x, hx⟩ : S)) :
    IsLocalRing S where
  isUnit_or_isUnit_of_add_one {x y} hxy :=
    (‹IsLocalRing R›.isUnit_or_isUnit_of_add_one congr(Subtype.val $hxy)).elim
      (fun hx ↦ Or.inl (h_unit x.val x.prop hx)) (fun hy ↦ Or.inr (h_unit y.val y.prop hy))
/-
**Subring.isLocalRing_of_unit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subring.isLocalRing_of_unit {R : Type*} [Ring R] [IsLocalRing R] (S : Subr
ing R) (h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (⟨x, hx⟩ : S))
 : IsLocalRing S
参数：S : Subring R；h_unit : forall (x : R) (hx : x in S), IsUnit x -> IsUnit (⟨x, 
hx⟩ : S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemiring.isLocalRing_of_unit`：Subsemiring.isLocalRing_of_unit {R : Ty
pe*} [Semiring R] [IsLocalRing R] (S : Subsemiring R) (h_unit : forall (x : R) (
hx : x in S), IsUnit …
-/
lemma Subring.isLocalRing_of_unit {R : Type*} [Ring R] [IsLocalRing R] (S : Subring R)
    (h_unit : ∀ (x : R) (hx : x ∈ S), IsUnit x → IsUnit (⟨x, hx⟩ : S)) :
    IsLocalRing S :=
  S.toSubsemiring.isLocalRing_of_unit h_unit
