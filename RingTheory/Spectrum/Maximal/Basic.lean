/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Maximal spectrum of a commutative (semi)ring

Basic properties the maximal spectrum of a ring.
-/

@[expose] public section

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
/-
**MaximalSpectrum.equivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `MaximalSpectrum`。
形式化陈述：equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where toFu
n I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal

--- 原说明 ---
The prime spectrum is in bijection with the set of prime ideals.
-/
def equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
/-
**MaximalSpectrum.range_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpectrum`。
形式化陈述：range_asIdeal : Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMax
imal}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
-/
theorem range_asIdeal : Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr <| hj ▸ j.isMaximal,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

variable {R}
/-
**MaximalSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `MaximalSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nonempty <| MaximalSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
/-
**MaximalSpectrum.toPrimeSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `MaximalSpectrum`。
形式化陈述：toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R
参数：x : MaximalSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from the maximal spectrum to the prime spectrum.
-/
def toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R :=
  ⟨x.asIdeal, x.isMaximal.isPrime⟩
/-
**MaximalSpectrum.toPrimeSpectrum_injective** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSp
ectrum`。
形式化陈述：toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MaximalSpectrum.mk.injEq`：∀ {R : Type u_1} [inst : CommSemiring R] (asId
eal : Ideal R) (isMaximal : asIdeal.IsMaximal) (asIdeal_1 : Ideal R)   (isMaxima
l_1 : asIdeal_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
-/
theorem toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using! PrimeSpectrum.ext_iff.mp h
/-
**MaximalSpectrum.isCoprime_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpectrum`。
形式化陈述：isCoprime_of_ne {I J : MaximalSpectrum R} (h : I != J) : IsCoprime I.1 J.1
参数：h : I != J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isCoprime_iff_sup_eq`：isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J
 = ⊤
· 使用定理 `Ideal.IsMaximal.coprime_of_ne`：∀ {α : Type u} [inst : Semiring α] {M M' 
: Ideal α}, M.IsMaximal → M'.IsMaximal → M ≠ M' → M ⊔ M' = ⊤
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MaximalSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Max
imalSpectrum R}, x.asIdeal = y.asIdeal → x = y
-/
theorem isCoprime_of_ne {I J : MaximalSpectrum R} (h : I ≠ J) : IsCoprime I.1 J.1 :=
  Ideal.isCoprime_iff_sup_eq.mpr <| I.2.coprime_of_ne J.2 <| mt MaximalSpectrum.ext h

end MaximalSpectrum

