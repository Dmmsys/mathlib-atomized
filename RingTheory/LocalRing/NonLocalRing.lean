/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!

# Non-local rings

This file gathers some results about non-local rings.

## Main results

- `not_isLocalRing_of_nontrivial_pi`: for an index type `ι` with at least two elements and
  an indexed family of (semi)rings `R : ι → Type*`, the indexed product (semi)ring
  `Π i, R i` is not local.
- `not_isLocalRing_of_prod_of_nontrivial`: the product of two nontrivial (semi)rings is not
  local.
- `not_isLocalRing_tfae`: the following conditions are equivalent for a commutative (semi)ring `R`:
    * `R` is not local,
    * the maximal spectrum of `R` is nontrivial,
    * `R` has two distinct maximal ideals.
- `exists_surjective_of_not_isLocalRing`: there exists a surjective ring homomorphism from
  a non-local commutative ring onto a product of two fields.

-/

public section

namespace IsLocalRing

/-- If two non-units sum to 1 in a (semi)ring `R` then `R` is not local. -/
/-
**IsLocalRing.not_isLocalRing_def** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：not_isLocalRing_def {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (h
b : ¬IsUnit b) (hab : a + b = 1) : ¬IsLocalRing R
参数：ha : ¬IsUnit a；hb : ¬IsUnit b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b

--- 原说明 ---
If two non-units sum to 1 in a (semi)ring `R` then `R` is not local.
-/
theorem not_isLocalRing_def {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b)
    (hab : a + b = 1) : ¬IsLocalRing R :=
  fun _ ↦ hb <| (isUnit_or_isUnit_of_add_one hab).resolve_left ha

/-- For an index type `ι` with at least two elements and an indexed family of (semi)rings
`R : ι → Type*`, the indexed product (semi)ring `Π i, R i` is not local. -/
/-
**IsLocalRing.not_isLocalRing_of_nontrivial_pi** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lRing`。
形式化陈述：not_isLocalRing_of_nontrivial_pi {ι : Type*} [Nontrivial ι] (R : ι -> Type
*) [forall i, Semiring (R i)] [forall i, Nontrivial (R i)] : ¬IsLocalRing (Π i, 
R i)
参数：R : ι -> Type*；R i；R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `IsLocalRing.not_isLocalRing_def`：not_isLocalRing_def {R : Type*} [Semiri
ng R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b) (hab : a + b = 1) : ¬IsLocalRi
ng R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
For an index type `ι` with at least two elements and an indexed family of (semi)
rings
`R : ι → Type*`, the indexed product (semi)ring `Π i, R i` is not local.
-/
theorem not_isLocalRing_of_nontrivial_pi {ι : Type*} [Nontrivial ι] (R : ι → Type*)
    [∀ i, Semiring (R i)] [∀ i, Nontrivial (R i)] : ¬IsLocalRing (Π i, R i) := by
  classical
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i ↦ if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i ↦ if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  exact not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

/-- The product of two nontrivial (semi)rings is not local. -/
/-
**IsLocalRing.not_isLocalRing_of_prod_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `I
sLocalRing`。
形式化陈述：not_isLocalRing_of_prod_of_nontrivial (R₁ R₂ : Type*) [Semiring R₁] [Semir
ing R₂] [Nontrivial R₁] [Nontrivial R₂] : ¬IsLocalRing (R₁ × R₂)
参数：R₁ R₂ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalRing.not_isLocalRing_def`：not_isLocalRing_def {R : Type*} [Semiri
ng R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b) (hab : a + b = 1) : ¬IsLocalRi
ng R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The product of two nontrivial (semi)rings is not local.
-/
theorem not_isLocalRing_of_prod_of_nontrivial (R₁ R₂ : Type*) [Semiring R₁] [Semiring R₂]
    [Nontrivial R₁] [Nontrivial R₂] : ¬IsLocalRing (R₁ × R₂) :=
  have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

/-- The following conditions are equivalent for a commutative (semi)ring `R`:
* `R` is not local,
* the maximal spectrum of `R` is nontrivial,
* `R` has two distinct maximal ideals.
-/
/-
**IsLocalRing.not_isLocalRing_tfae** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：not_isLocalRing_tfae {R : Type*} [CommSemiring R] [Nontrivial R] : List.TF
AE [ ¬IsLocalRing R, Nontrivial (MaximalSpectrum R), exists m₁ m₂ : Ideal R, m₁.
IsMaximal ∧ m₂.IsMaximal ∧ m₁ != m₂]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `IsLocalRing.of_singleton_maximalSpectrum`：of_singleton_maximalSpectrum [
Subsingleton (MaximalSpectrum R)] [Nonempty (MaximalSpectrum R)] : IsLocalRing R
· 使用定理 `MaximalSpectrum.instNonemptyOfNontrivial`：∀ {R : Type u_1} [inst : CommS
emiring R] [Nontrivial R], Nonempty (MaximalSpectrum R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
The following conditions are equivalent for a commutative (semi)ring `R`:
* `R` is not local,
* the maximal spectrum of `R` is nontrivial,
* `R` has two distinct maximal ideals.
-/
theorem not_isLocalRing_tfae {R : Type*} [CommSemiring R] [Nontrivial R] :
    List.TFAE [
      ¬IsLocalRing R,
      Nontrivial (MaximalSpectrum R),
      ∃ m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ m₁ ≠ m₂] := by
  tfae_have 1 → 2
  | h => not_subsingleton_iff_nontrivial.mp fun _ ↦ h of_singleton_maximalSpectrum
  tfae_have 2 → 3
  | ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, h⟩ => ⟨m₁, m₂, ⟨hm₁, hm₂, fun _ ↦ h (by congr)⟩⟩
  tfae_have 3 → 1
  | ⟨m₁, m₂, ⟨hm₁, hm₂, h⟩⟩ => fun _ ↦ h <| (eq_maximalIdeal hm₁).trans (eq_maximalIdeal hm₂).symm
  tfae_finish

/-- There exists a surjective ring homomorphism from a non-local commutative ring onto a product
of two fields. -/
/-
**IsLocalRing.exists_surjective_of_not_isLocalRing.** 是 Mathlib 中的一个定理，位于命名空间 `I
sLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There exists a surjective ring homomorphism from a non-local commutative ring on
to a product
of two fields.
-/
theorem exists_surjective_of_not_isLocalRing.{u} {R : Type u} [CommRing R] [Nontrivial R]
    (h : ¬IsLocalRing R) :
    ∃ (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R →+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := (not_isLocalRing_tfae.out 0 2).mp h
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ <| Ideal.isCoprime_of_isMaximal hm₁m₂
  let f := e.toRingHom.comp <| Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

end IsLocalRing

