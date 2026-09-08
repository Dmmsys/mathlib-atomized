/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.QuasiFinite.Polynomial
public import Mathlib.Algebra.Algebra.Shrink

/-!
# Algebraic Zariski's Main Theorem

The statement of Zariski's main theorem is the following:
Given a finite type `R`-algebra `S`, and `p` a prime of `S` such that `S` is quasi-finite at `R`,
then there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.

We follow https://stacks.math.columbia.edu/tag/00PI and proceed in the following steps

1. `Algebra.ZariskisMainProperty.of_adjoin_eq_top`:
  The case where `S = R[X]/I`.
  The key is `Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt`
  which shows that there exists some `g ∈ I` such that some coefficient `gᵢ ∉ p`.
  Then one basically takes `f = gᵢ` and `g` becomes monic in `R[1/gᵢ][X]` up to some minor technical
  issues, and then `S[1/gᵢ]` is basically integral over `R[1/gᵢ]`.
2. `Algebra.ZariskisMainProperty.of_algHom_polynomial`:
  The case where `S` is finite over `R⟨x⟩` for some `x : S`.
  The following key results are first established:
  - `isStronglyTranscendental_mk_radical_conductor`:
    Let `𝔣` be the conductor of `x` (i.e. the largest `S`-ideal in `R⟨x⟩`).
    `x` as an element of `S/√𝔣` is strongly transcendental over `R`.
  - `Algebra.not_quasiFiniteAt_of_stronglyTranscendental`:
    If `S` is reduced, then `x : S` is not strongly transcendental over `R`.
    One first reduces to when `R ⊆ S` are domains, and then to when `R` is integrally closed.
    A going down theorem is now available, which could be applied to
    `Polynomial.map_under_lt_comap_of_quasiFiniteAt`:`(p ∩ R)[X] < p ∩ R<x>` to get a contradiction.

  The second result applied to `S/√𝔣` together with the first result implies that
  `p` does not contain `𝔣`.
  The claim then follows from `Localization.localRingHom_bijective_of_not_conductor_le`.
3. `Algebra.ZariskisMainProperty.of_algHom_mvPolynomial`:
  The case where `S` is finite over `R⟨x₁,...,xₙ⟩`. This is proved using induction on `n`.

## Main definition and results
- `Algebra.ZariskisMainProperty`:
  We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
  if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`.
- `Algebra.ZariskisMainProperty.of_finiteType`:
  If `S` is finite type over `R` and quasi-finite at `p`, then `ZariskisMainProperty` holds.
- `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`:
  If `S` is finite type over `R` and quasi-finite at `p`,
  then there exists a subalgebra `S'` of `R` that is finitely generated as an `R`-module,
  and some `r ∈ S'` such that `r ∉ p` and `S'[1/r] = S[1/r]`.
-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

namespace Algebra

variable (R) in
/-- We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`. -/
/-
**Algebra.ZariskisMainProperty** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：ZariskisMainProperty (p : Ideal S) : Prop
参数：p : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an `R` algebra `S` satisfies the Zariski's main property at a prime 
`p` of `S`
if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S
'[1/r] = S[1/r]`.
-/
def ZariskisMainProperty (p : Ideal S) : Prop :=
  ∃ r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)
/-
**Algebra.zariskisMainProperty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：zariskisMainProperty_iff {p : Ideal S} : ZariskisMainProperty R p ↔ exists
 r ∉ p, IsIntegral R r ∧ forall x, exists m, IsIntegral R (r ^ m * x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `IsLocalization.map_injective_of_injective`：map_injective_of_injective (h
 : Function.Injective g) [IsLocalization (M.map g) Q] : Function.Injective (map 
Q g M.le_comap_map : S -> Q)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsLocalization.Away.instMapRingHomPowersOfCoe`：∀ {A : Type u_5} [inst : 
CommSemiring A] {B : Type u_6} [inst_1 : CommSemiring B] (Bₚ : Type u_8)   [inst
_2 : CommSemiring Bₚ] [inst_3 : Alg…
· 使用引理 `Localization.awayMap_surjective_iff`：awayMap_surjective_iff {f : R ->+* 
S} {r : R} : Function.Surjective (Localization.awayMap f r) ↔ forall a, exists b
 m, f b = f r ^ m * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zariskisMainProperty_iff {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, IsIntegral R r ∧ ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp ↦ ?_
  rw [Function.Bijective, and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective),
    Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]
/-
**Algebra.zariskisMainProperty_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：zariskisMainProperty_iff' {p : Ideal S} : ZariskisMainProperty R p ↔ exist
s r ∉ p, forall x, exists m, IsIntegral R (r ^ m * x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Algebra.zariskisMainProperty_iff`：zariskisMainProperty_iff {p : Ideal S}
 : ZariskisMainProperty R p ↔ exists r ∉ p, IsIntegral R r ∧ forall x, exists m,
 IsIntegral R (r ^ m *…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegral.pow_iff`：IsIntegral.pow_iff {x : A} {n : Nat} (hn : 0 < n) : 
IsIntegral R (x ^ n) ↔ IsIntegral R x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
lemma zariskisMainProperty_iff' {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  refine zariskisMainProperty_iff.trans (exists_congr fun r ↦ and_congr_right fun hrp ↦
    and_iff_right_of_imp fun H ↦ ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn
/-
**Algebra.zariskisMainProperty_iff_exists_saturation_eq_top** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra`。
形式化陈述：zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} : Zariskis
MainProperty R p ↔ exists r ∉ p, exists h : IsIntegral R r, (integralClosure R S
).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∃ h : IsIntegral R r,
      (integralClosure R S).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤ := by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]
/-
**Algebra.ZariskisMainProperty.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.ZariskisMainProperty`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T] [Algebra.IsIntegral R S]   {p 
: Ideal T}, Algebra.ZariskisMainProperty S p → Algebra.ZariskisMainProperty R p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.zariskisMainProperty_iff'`：zariskisMainProperty_iff' {p : Ideal 
S} : ZariskisMainProperty R p ↔ exists r ∉ p, forall x, exists m, IsIntegral R (
r ^ m * x)
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma ZariskisMainProperty.restrictScalars [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] {p : Ideal T} (H : ZariskisMainProperty S p) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x ↦ ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩
/-
**Algebra.ZariskisMainProperty.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Zariskis
MainProperty`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime],   A
lgebra.ZariskisMainProperty R (Ideal.under S p) →     (∃ r ∉ Ideal.under S p, ⊥.
saturation (Submonoid.powers ((algebraMap S T) r)) ⋯ = ⊤) →       Algebra.Zarisk
isMainProperty R p
参数：p : Ideal T；Ideal.under S p；∃ r ∉ Ideal.under S p, ⊥.saturation (Submonoid.po
wers ((algebraMap S T) r)) ⋯ = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.zariskisMainProperty_iff'`：zariskisMainProperty_iff' {p : Ideal 
S} : ZariskisMainProperty R p ↔ exists r ∉ p, forall x, exists m, IsIntegral R (
r ^ m * x)
· 使用引理 `Algebra.zariskisMainProperty_iff`：zariskisMainProperty_iff {p : Ideal S}
 : ZariskisMainProperty R p ↔ exists r ∉ p, IsIntegral R r ∧ forall x, exists m,
 IsIntegral R (r ^ m *…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 49 条，此处仅展示前 30 条）
-/
lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
    (h₁ : ZariskisMainProperty R (p.under S))
    (h₂ : ∃ r ∉ p.under S, (⊥ : Subalgebra S T).saturation (.powers (algebraMap _ _ r))
      (by simp [Submonoid.powers_le]) = ⊤) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x ↦ ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstance : (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)
/-
**Algebra.ZariskisMainProperty.of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
ZariskisMainProperty`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal S)   [p.IsPrime] [Algebra.IsIntegral R S], Alg
ebra.ZariskisMainProperty R p
参数：p : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.zariskisMainProperty_iff'`：zariskisMainProperty_iff' {p : Ideal 
S} : ZariskisMainProperty R p ↔ exists r ∉ p, forall x, exists m, IsIntegral R (
r ^ m * x)
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
lemma ZariskisMainProperty.of_isIntegral (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S] :
    ZariskisMainProperty R p :=
  zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ ↦ ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

end Algebra

section IsStronglyTranscendental

variable (φ : R[X] →ₐ[R] S) (t : S) (p r : R[X])

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a map `φ : R[X] →ₐ[R] S`. Suppose `t = φ r / φ p` is integral over `R[X]` where
`p` is monic with `deg p > deg r`, then `t` is also integral over `R`. -/
/-
**isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt (ht : φ.IsIntegralEl
em t) (hpm : p.Monic) (hpr : r.natDegree < p.natDegree) (hp : φ p * t = φ r) : I
sIntegral R t
参数：ht : φ.IsIntegralElem t；hpm : p.Monic；hpr : r.natDegree < p.natDegree；hp : φ 
p * t = φ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.Away.mul_invSelf`：mul_invSelf : algebraMap R S x * invSel
f x = 1
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `isIntegral_zero`：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `le_integralClosure_iff_isIntegral`：le_integralClosure_iff_isIntegral {S 
: Subalgebra R A} : S <= integralClosure R A ↔ Algebra.IsIntegral R S
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_integralClosure_iff`：mem_integralClosure_iff {a : A} : a in integral
Closure R A ↔ IsIntegral R a
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Polynomial.Monic.sub_of_left`：∀ {R : Type u} [inst : Ring R] {p q : Poly
nomial R}, p.Monic → q.degree < p.degree → (p - q).Monic
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Given a map `φ : R[X] →ₐ[R] S`. Suppose `t = φ r / φ p` is integral over `R[X]` 
where
`p` is monic with `deg p > deg r`, then `t` is also integral over `R`.
-/
lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
    (ht : φ.IsIntegralElem t) (hpm : p.Monic)
    (hpr : r.natDegree < p.natDegree) (hp : φ p * t = φ r) : IsIntegral R t := by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  let : Algebra R₁ R₂ := R₂.algebra
  let : Algebra R₂ St := R₂.toAlgebra
  let : Algebra R₁ St := R₁.toAlgebra
  have : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, eval₂_map, ← map_zero (algebraMap S St), ← hq',
      hom_eval₂]
    congr 1
    ext <;> simp [-Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)

@[stacks 00PT]
/-
**exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (ht : φ.IsIntegra
lElem t) (hpm : p.Monic) (hp : φ p * t in φ.range) : exists q, IsIntegral R (t -
 φ q)
参数：ht : φ.IsIntegralElem t；hpm : p.Monic；hp : φ p * t in φ.range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt`：isIntegral_of_isI
ntegralElem_of_monic_of_natDegree_lt (ht : φ.IsIntegralElem t) (hpm : p.Monic) (
hpr : r.natDegree < p.natDegree) (hp : φ p …
· 使用定理 `RingHom.IsIntegralElem.sub`：RingHom.IsIntegralElem.sub {x y : S} (hx : f
.IsIntegralElem x) (hy : f.IsIntegralElem y) : f.IsIntegralElem (x - y)
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
· 使用定理 `Polynomial.natDegree_modByMonic_lt`：natDegree_modByMonic_lt (p : R[X]) {
q : R[X]} (hmq : Monic q) (hq : q != 1) : natDegree (p %ₘ q) < q.natDegree
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : φ p * t ∈ φ.range) :
    ∃ q, IsIntegral R (t - φ q) := by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p)) p (r %ₘ p)
    (ht.sub _ φ.isIntegralElem_map) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div])⟩

open IsScalarTower in
attribute [local simp] IsLocalization.map_eq aeval_algebraMap_apply aeval_algHom_apply in
@[stacks 00PV]
/-
**exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_r
ange (ht : φ.IsIntegralElem t) (hp : φ p * t in φ.range) : exists q n, IsIntegra
l R (p.leadingCoeff ^ n • t - φ q)
参数：ht : φ.IsIntegralElem t；hp : φ p * t in φ.range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.Away.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (
S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {P : Type u_3}   
[inst_3 : CommSemi…
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用引理 `exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range`：exists_isInteg
ral_sub_of_isIntegralElem_of_mul_mem_range (ht : φ.IsIntegralElem t) (hpm : p.Mo
nic) (hp : φ p * t in φ.range) : exists q, IsI…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 90 条，此处仅展示前 30 条）
-/
lemma exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    (ht : φ.IsIntegralElem t) (hp : φ p * t ∈ φ.range) :
    ∃ q n, IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
  set a := p.leadingCoeff
  let R' := Localization.Away a
  let S' := Localization.Away (algebraMap R S a)
  let : Algebra R' S' := (Localization.awayMap (algebraMap R S) a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq (by
    simp +zetaDelta [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← algebraMap_apply R S])
  have ha : IsUnit (algebraMap R R' a) := IsLocalization.Away.algebraMap_isUnit a
  have H : (aeval ((algebraMap S S') (φ X))).toRingHom.comp (mapRingHom (algebraMap R R')) =
    (algebraMap S S').comp φ := by ext <;>
      simp [-Polynomial.algebraMap_apply, ← Polynomial.algebraMap_eq, ← algebraMap_apply]
  obtain ⟨q, hq⟩ := exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (R := R')
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map, H, ← hom_eval₂, ← AlgHom.toRingHom_eq_coe, hq, map_zero]) (by
      nontriviality R'
      simp [Monic, leadingCoeff_C_mul_of_isUnit,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ ha.ne_zero, a]) (by
      obtain ⟨r, hr : φ r = _⟩ := hp
      use C ha.unit⁻¹.1 * mapRingHom (algebraMap R R') r
      simp [aeval_algebraMap_apply, aeval_algHom_apply, hr, mul_assoc])
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := IsLocalization.integerNormalization_spec (.powers a) q
  generalize IsLocalization.integerNormalization (.powers a) q = q' at e
  have : IsIntegral R' ((algebraMap S S') (a ^ n • t - φ q')) := by
    have : algebraMap S S' (φ q') = (algebraMap R S' a) ^ n * aeval (algebraMap S S' (φ X)) q := by
      simpa [Algebra.smul_def, aeval_algebraMap_apply, aeval_algHom_apply, ← algebraMap_apply] using
        congr(aeval (algebraMap S S' (φ X)) $e)
    simpa [Algebra.smul_def, ← mul_sub, ← algebraMap_apply, this] using
      (isIntegral_algebraMap (A := S') (x := algebraMap R R' a ^ n)).mul hq
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := this.exists_multiple_integral_of_isLocalization (.powers a) _
  simp only [Algebra.smul_def, Submonoid.smul_def, algebraMap_apply R S S', ← map_mul] at hm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (.powers a) hm
  refine ⟨C a ^ (k + m) * q', k + m + n, ?_⟩
  convert! hk using 1
  simp only [Algebra.smul_def, map_pow, ← Polynomial.algebraMap_eq, map_mul, AlgHom.commutes]
  ring

@[stacks 00PX]
/-
**exists_leadingCoeff_pow_smul_mem_conductor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_leadingCoeff_pow_smul_mem_conductor (hRS : integralClosure R S = ⊥)
 -- `IsIntegrallyClosedIn` but without injective assumption (hφ : φ.toRingHom.Fi
nite) (hp : φ p * t in conductor R (φ X)) : exists n, p.leadingCoeff ^ n • t in 
conductor R (φ X)
参数：hRS : integralClosure R S = ⊥；hφ : φ.toRingHom.Finite；hp : φ p * t in conduct
or R (φ X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.adjoin_X`：∀ {R : Type u} [inst : CommSemiring R], R[Polynomia
l.X] = ⊤
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用引理 `exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem
_range`：exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem
_range (ht : φ.IsIntegralElem t) (hp : φ p * t in φ.range) : exists …
· 使用定理 `RingHom.Finite.to_isIntegral`：RingHom.Finite.to_isIntegral (h : f.Finite
) : f.IsIntegral
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
（共 65 条，此处仅展示前 30 条）
-/
lemma exists_leadingCoeff_pow_smul_mem_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (hφ : φ.toRingHom.Finite) (hp : φ p * t ∈ conductor R (φ X)) :
    ∃ n, p.leadingCoeff ^ n • t ∈ conductor R (φ X) := by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : ∃ n, p.leadingCoeff ^ n • (t * x) ∈ φ.range := by
    have : φ p * t * x ∈ φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _ p
        (hφ.to_isIntegral (t * x)) (by convert! this using 1; ring)
    obtain ⟨r, hr : algebraMap _ _ r = _⟩ := hRS.le hn
    exact ⟨n, (C r + q), by simp [← Polynomial.algebraMap_eq, -Polynomial.algebraMap_apply, hr]⟩
  choose n hn using this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := S)
  refine ⟨s.sup n, fun x ↦ ?_⟩
  rw [← AlgHom.map_adjoin_singleton, adjoin_X, Algebra.map_top, Algebra.smul_mul_assoc]
  induction hs.ge (Set.mem_univ x) using Submodule.span_induction with
  | mem x h =>
    rw [← Nat.sub_add_cancel (s.le_sup h), pow_add, mul_smul]
    exact Subalgebra.smul_mem _ (hn _) _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add, smul_add] using add_mem hx hy
  | smul a x hx IH =>
    rw [mul_smul_comm, smul_comm, Algebra.smul_def]
    exact mul_mem (AlgHom.mem_range_self _ _) IH

@[stacks 00PY]
/-
**exists_leadingCoeff_pow_smul_mem_radical_conductor** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：exists_leadingCoeff_pow_smul_mem_radical_conductor (hRS : integralClosure 
R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption (hφ : φ.toRi
ngHom.Finite) (hp : φ p * t in (conductor R (φ X)).radical) (i : Nat) : p.coeff 
i • t in (conductor R (φ X)).radical
参数：hRS : integralClosure R S = ⊥；hφ : φ.toRingHom.Finite；hp : φ p * t in (conduc
tor R (φ X)).radical；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `exists_leadingCoeff_pow_smul_mem_conductor`：exists_leadingCoeff_pow_smul
_mem_conductor (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but wit
hout injective assumption (hφ : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `mul_smul_mul_comm`：mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScala
rTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) : 
(a * b)…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
（共 47 条，此处仅展示前 30 条）
-/
lemma exists_leadingCoeff_pow_smul_mem_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (hφ : φ.toRingHom.Finite) (hp : φ p * t ∈ (conductor R (φ X)).radical) (i : ℕ) :
    p.coeff i • t ∈ (conductor R (φ X)).radical := by
  wlog hi : i = p.natDegree generalizing p i
  · clear hi
    simp only [forall_eq, coeff_natDegree] at this
    induction hpn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n IH =>
    cases n with
    | zero =>
      obtain hi' | hi' := lt_or_ge p.natDegree i
      · simp [coeff_eq_zero_of_natDegree_lt hi']
      · simpa [← coeff_natDegree, hpn, show i = 0 by lia] using this _ hp
    | succ n =>
      obtain hi' | hi' := eq_or_ne i p.natDegree
      · simpa [hi'] using this _ hp
      have : φ p.eraseLead * t ∈ (conductor R (φ X)).radical := by
        simp only [← self_sub_C_mul_X_pow, map_sub, ← algebraMap_eq, map_mul, AlgHom.commutes,
          map_pow, sub_mul, mul_right_comm _ _ t, ← Algebra.smul_def _ t]
        exact sub_mem hp (Ideal.mul_mem_right _ _ (this _ hp))
      simpa [eraseLead_coeff, hi'] using
        IH _ ((eraseLead_natDegree_le _).trans_lt (by lia)) _ this rfl
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor φ (t ^ n) (p ^ n) hRS hφ
    (by simpa [mul_pow] using hn)
  by_cases hpn : p.leadingCoeff ^ n = 0
  · use n; simp [_root_.smul_pow, hpn, hi]
  rw [leadingCoeff_pow' hpn, ← pow_mul] at hk
  refine ⟨n * k + n, ?_⟩
  rw [_root_.smul_pow, pow_add, add_comm, pow_add, mul_smul_mul_comm, hi]
  exact Ideal.mul_mem_right _ _ hk

@[stacks 00PY]
/-
**isStronglyTranscendental_mk_radical_conductor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isStronglyTranscendental_mk_radical_conductor (hRS : integralClosure R S =
 ⊥) -- `IsIntegrallyClosedIn` but without injective assumption (x : S) (hx : (ae
val (R
参数：hRS : integralClosure R S = ⊥；x : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `exists_leadingCoeff_pow_smul_mem_radical_conductor`：exists_leadingCoeff_
pow_smul_mem_radical_conductor (hRS : integralClosure R S = ⊥) -- `IsIntegrallyC
losedIn` but without injective assumptio…
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma isStronglyTranscendental_mk_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (x : S) (hx : (aeval (R := R) x).Finite) :
    IsStronglyTranscendental R (Ideal.Quotient.mk (conductor R x).radical x) := by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e ↦ ?_
  rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at e
  ext i
  simpa [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor _ u p hRS hx
      (by simpa using e) i

end IsStronglyTranscendental

namespace Algebra

attribute [local instance] Polynomial.isLocalization Polynomial.algebra

section not_quasiFiniteAt

/-- Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead. -/
/-
**Algebra.not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClo
sed** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead.
-/
private lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed
    [FaithfulSMul R S] [IsIntegrallyClosed R] [IsDomain S]
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
      ¬ IsStronglyTranscendental R x := by
  intro hx
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have hf' : Function.Injective (aeval (R := R) x) := (injective_iff_map_eq_zero _).mpr
    fun p hp ↦ not_not.mp fun hp' ↦ hx.transcendental ⟨p, hp', hp⟩
  generalize hf : aeval (R := R) x = f at *
  obtain rfl : f X = x := by simp [← hf]
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite R[X] S := RingHom.finite_algebraMap.mpr hx'
  have : FaithfulSMul R[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro p hp
    by_contra hp'
    exact hx.transcendental ⟨p, hp', by rwa [aeval_algHom_apply, aeval_X_left_apply]⟩
  have : (P.under R).map C < P.under R[X] := map_under_lt_comap_of_weaklyQuasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.WeaklyQuasiFiniteAt.eq_of_le_of_under_eq (R := R) hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]

/-- This asks for an explicit `K = Frac(R)`, `L = Frac(S)`,
`R'` the integral closure of `R` in `K`, and `S' ⊆ L` the subalgebra spanned by `R'` and `S`,
to aid typeclass synthesis.

Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead. -/
@[stacks 00Q1]
/-
**Algebra.not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux** 
是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This asks for an explicit `K = Frac(R)`, `L = Frac(S)`,
`R'` the integral closure of `R` in `K`, and `S' ⊆ L` the subalgebra spanned by 
`R'` and `S`,
to aid typeclass synthesis.

Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead.
-/
private lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K] [IsFractionRing S L]
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S'] [Algebra R S']
    [Algebra S' L] [Algebra R' L] [IsScalarTower R' S' L] [Algebra R' K] [IsScalarTower R' K L]
    [IsScalarTower R R' S'] [FaithfulSMul S' L] [IsIntegralClosure R' R K]
    [IsScalarTower R R' K]
    (f : S →ₐ[R] S') (hf₁ : Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _))
    (hf₂ : (algebraMap S' L).comp f.toRingHom = algebraMap _ _)
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x := by
  intro hx
  have := (FaithfulSMul.algebraMap_injective S' L).isDomain
  have := (FaithfulSMul.algebraMap_injective R K).isDomain
  have : Algebra.IsIntegral R R' := IsIntegralClosure.isIntegral_algebra _ K
  have : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsIntegralClosure.algebraMap_injective R' R K)
  have : FaithfulSMul R R' := .tower_bot _ _ K
  have : FaithfulSMul R' L := .trans _ K _
  have : FaithfulSMul R' S' := .tower_bot _ _ L
  have : IsIntegrallyClosedIn R' K := .of_isIntegralClosure R
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _
  have hf₃ : Function.Injective f :=
    .of_comp (f := algebraMap S' L) (hf₂ ▸ FaithfulSMul.algebraMap_injective S L:)
  have hf₄ : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hf₁.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := IsScalarTower.toAlgHom R' S' L) (FaithfulSMul.algebraMap_injective S' L) ?_
    dsimp
    rw [show algebraMap S' L (f x) = algebraMap _ _ x from congr($hf₂ x)]
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert!
      ((RingHom.Finite.of_surjective g.toRingHom hf₁).comp
            (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite
              hx')).comp
        (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf₄.comap_surjective hf₃ ⟨P, ‹_›⟩
  suffices WeaklyQuasiFiniteAt R' Q from
    not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed H₂ Q H₁
  have : Algebra.WeaklyQuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ <| by
    rw [Ideal.comap_comap]
    convert! congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks (Q.comap g.toRingHom) _ g
    (RingHom.surjectiveOnStalks_of_surjective hf₁) rfl

set_option backward.isDefEq.respectTransparency false in
nonrec lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt [IsReduced S]
    {x : S} (hx' : (aeval (R := R) x).toRingHom.Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x := by
  wlog hS : IsDomain S ∧ FaithfulSMul R S
  · intro hx
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
    have inst := hp.1.1
    have inst : (P.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa)
    have inst : WeaklyQuasiFiniteAt (R ⧸ Ideal.under R p) (Ideal.map (Ideal.Quotient.mk p) P) := by
      suffices Algebra.WeaklyQuasiFiniteAt R (P.map (Ideal.Quotient.mk p)) from
        .of_restrictScalars R _ _
      refine .of_surjectiveOnStalks P _ (Ideal.Quotient.mkₐ _ _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) ?_
      refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine this (R := R ⧸ p.under R) ?_ (P.map (Ideal.Quotient.mk p)) ⟨inferInstance, inferInstance⟩
      ((isStronglyTranscendental_mk_of_mem_minimalPrimes hx p hp).of_surjective_left
        Ideal.Quotient.mk_surjective)
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (Ideal.Quotient.mk _)) ?_
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := p))).comp hx'
    ext <;> simp
  cases hS
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  let R' := integralClosure R K
  let S' : Subalgebra R' L := Algebra.adjoin R' (algebraMap S L).range
  let f : S →ₐ[R] S' := (IsScalarTower.toAlgHom R S L).codRestrict (S'.restrictScalars R) fun x ↦ by
    simpa using show algebraMap S L x ∈ S' from Algebra.subset_adjoin ⟨x, rfl⟩
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _
  have hf : Function.Surjective g := by
    rw [← AlgHom.range_eq_top,
      ← (Subalgebra.map_injective (f := S'.val) Subtype.val_injective).eq_iff, Algebra.map_top]
    refine le_antisymm (Set.image_subset_range S'.val g.range) ?_
    simp only [RingHom.coe_range, Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
      Subalgebra.coe_val, AlgHom.coe_range, Set.range_subset_iff, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, S']
    exact fun y ↦ ⟨1 ⊗ₜ y, by simp [g, S']; rfl⟩
  exact not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux K L f hf rfl hx' P

@[stacks 00Q2]
nonrec lemma not_isStronglyTranscendental_of_quasiFiniteAt [IsReduced S]
    {x : S} (hx' : (aeval (R := R) x).toRingHom.Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x :=
  not_isStronglyTranscendental_of_weaklyQuasiFiniteAt hx' P

end not_quasiFiniteAt

section FixedUniverse

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/-
**Algebra.ZariskisMainProperty.of_adjoin_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
ra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ZariskisMainProperty.of_adjoin_eq_top
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p]
    (x : S) (hx : Algebra.adjoin R {x} = ⊤) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p x ?_ (integralClosure_idem (R := R)))
    suffices ⊤ ≤ (Algebra.adjoin (integralClosure R S) {x}).restrictScalars R from
      top_le_iff.mp fun x _ ↦ (Subalgebra.mem_restrictScalars _).mp (this trivial)
    refine hx.ge.trans ?_
    rw [Algebra.restrictScalars_adjoin]
    exact Algebra.adjoin_mono (by simp)
  have H₀ : Function.Surjective (aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  have ⟨f, (hf : aeval x f = 0), hfp⟩ := SetLike.not_le_iff_exists.mp
    (Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt _ H₀ p)
  obtain ⟨n, hfn⟩ : ∃ x, algebraMap R S (f.coeff x) ∉ p := by simpa [Ideal.mem_map_C_iff] using! hfp
  clear hfp
  induction hm : f.natDegree using Nat.strong_induction_on generalizing f n with | h m IH =>
  obtain (_ | m) := m
  · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp hm
    cases n <;> aesop
  by_cases Hfp : algebraMap _ _ f.leadingCoeff ∈ p
  · obtain ⟨a, ha⟩ := H.le (isIntegral_leadingCoeff_smul f x hf)
    refine IH _ ?_ (f.eraseLead + C a * X ^ m) (hm := rfl) ?_ n ?_
    · suffices f.eraseLead.natDegree ≤ m by compute_degree!
      exact (eraseLead_natDegree_le ..).trans (by lia)
    · simp [← self_sub_monomial_natDegree_leadingCoeff, hf, hm, pow_succ', ← Algebra.smul_def,
        ← Algebra.smul_mul_assoc, ← ha]
    · suffices algebraMap R S (f.coeff n) + algebraMap R S (if n = m then a else 0) ∉ p by
        simpa [eraseLead_coeff, show n ≠ f.natDegree by rintro rfl; exact hfn (by simpa)]
      rwa [Ideal.add_mem_iff_left]
      split_ifs
      · convert p.mul_mem_right x Hfp
        simpa [Algebra.smul_def] using! ha
      · simp
  · refine zariskisMainProperty_iff_exists_saturation_eq_top.mpr ⟨_, Hfp, isIntegral_algebraMap, ?_⟩
    rw [← top_le_iff, ← hx]
    refine Algebra.adjoin_singleton_le ⟨_, ⟨1, rfl⟩, ?_⟩
    simpa [Algebra.smul_def] using! isIntegral_leadingCoeff_smul f x hf

-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/-
**Algebra.ZariskisMainProperty.of_algHom_polynomial** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ZariskisMainProperty.of_algHom_polynomial
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p]
    (f : R[X] →ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p (aeval (f X)) ?_ (integralClosure_idem (R := R)))
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (algebraMap R _)) ?_
    convert! (show f.toRingHom.Finite from hf)
    ext <;> simp [show ∀ x, f (C x) = algebraMap _ _ x from f.commutes]
  replace hf : ¬ conductor R (f X) ≤ p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    set J := (conductor R (f X)).radical
    have inst : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ J) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    have inst : WeaklyQuasiFiniteAt R (p.map (Ideal.Quotient.mk J)) := by
      refine .of_surjectiveOnStalks p _ (Ideal.Quotient.mkₐ R _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine not_isStronglyTranscendental_of_weaklyQuasiFiniteAt ?_ (p.map (Ideal.Quotient.mk J))
      (isStronglyTranscendental_mk_radical_conductor H (f X) (by convert! hf; ext; simp))
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))).comp hf
      using 1
    ext <;> simp [show ∀ x, f (C x) = algebraMap _ _ x from f.commutes, J]
  obtain ⟨x, hx, hxp⟩ := SetLike.not_le_iff_exists.mp hf
  replace hx (a : _) : x * a ∈ f.range := by simpa [← AlgHom.map_adjoin_singleton f] using hx a
  refine ZariskisMainProperty.trans (S := f.range) _ ?_ ?_
  · have : Algebra.WeaklyQuasiFiniteAt R (p.under f.range) := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under f.range) p
      let e : Localization.AtPrime (p.under f.range) ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          (Localization.localRingHom_bijective_of_not_conductor_le hf
            (by simp [← AlgHom.map_adjoin_singleton f]) _)
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    refine .of_adjoin_eq_top _ ⟨f X, X, rfl⟩ ?_
    simp [← (Subalgebra.map_injective (f := Subalgebra.val _) Subtype.val_injective).eq_iff,
      ← AlgHom.map_adjoin_singleton f, Subalgebra.range_val]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ ↦ ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s

open scoped Pointwise in
-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/-
**Algebra.ZariskisMainProperty.of_algHom_mvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ZariskisMainProperty.of_algHom_mvPolynomial
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  classical
  induction n generalizing R S with
  | zero =>
    have : Module.Finite R S := by
      rw [← RingHom.finite_algebraMap]
      convert! RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ (MvPolynomial.C_surjective _))
      exact f.comp_algebraMap.symm
    exact .of_isIntegral _
  | succ n IH =>
    let f' := f.comp (MvPolynomial.finSuccEquiv _ _).symm.toAlgHom
    let := (f'.toRingHom.comp C).toAlgebra
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r ↦
      (f.commutes r).symm.trans congr(f ($(MvPolynomial.finSuccEquiv_comp_C_eq_C n) r)).symm
    let f'' : (MvPolynomial (Fin n) R)[X] →ₐ[MvPolynomial (Fin n) R] S :=
      ⟨f'.toRingHom, fun _ ↦ rfl⟩
    have : Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin n) R) p := by
      exact .of_restrictScalars R _ _
    have := ZariskisMainProperty.of_algHom_polynomial p f''
      (RingHom.Finite.comp hf (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.finite)
    choose r hrp hr m hm using zariskisMainProperty_iff.mp this
    obtain ⟨⟨s, hs⟩⟩ : Algebra.FiniteType R S := by
      rw [← RingHom.finiteType_algebraMap, ← f.comp_algebraMap]
      exact RingHom.FiniteType.comp hf.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
    let R' : Subalgebra R S :=
      Algebra.adjoin R ↑(Finset.univ.image (f ∘ .X ∘ Fin.succ) ∪ r ^ (s.sup m) • s ∪ {r})
    have hrR' : r ∈ R' := Algebra.subset_adjoin (by simp)
    have : Algebra.WeaklyQuasiFiniteAt R (p.under R') := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under R') p
      let e : Localization.AtPrime (p.under R') ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _) <| by
          refine Localization.localRingHom_bijective_of_saturated_inf_eq_top _ ?_ _
          rw [← top_le_iff, ← hs, Algebra.adjoin_le_iff]
          intro x hx
          refine ⟨r ^ (s.sup m), pow_mem (by exact ⟨hrp, hrR'⟩) _, Algebra.subset_adjoin ?_⟩
          simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    let φ : MvPolynomial (Fin n) R →ₐ[R] R' :=
      MvPolynomial.aeval fun i ↦ ⟨f (.X i.succ), Algebra.subset_adjoin (by simp)⟩
    have := IH (R := R) (S := R') (p.under R') φ <| by
      refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
      · let := φ.toAlgebra
        have : IsScalarTower (MvPolynomial (Fin n) R) R' S := .of_algebraMap_eq' <| by
          ext <;> simp [φ, (f'.toRingHom.comp C).algebraMap_toAlgebra, φ.algebraMap_toAlgebra, f',
            MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft]
        refine algebraMap_isIntegral_iff.mpr (integralClosure_eq_top_iff.mp ?_)
        apply Subalgebra.restrictScalars_injective R
        rw [← (Subalgebra.map_injective (f := R'.val) Subtype.val_injective).eq_iff]
        simp only [Subalgebra.restrictScalars_top, Algebra.map_top]
        refine le_antisymm (Set.image_subset_range _ _) ?_
        suffices (∀ (a : Fin n), IsIntegral (MvPolynomial (Fin n) R) (f (MvPolynomial.X a.succ))) ∧
            ∀ a ∈ s, IsIntegral (MvPolynomial (Fin n) R) (r ^ s.sup m * a) by
          simp +contextual only [Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
            Subalgebra.coe_val, Set.subset_def, SetLike.mem_coe, Algebra.mem_adjoin_of_mem,
            Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, R']
          simpa [R', mem_integralClosure_iff,
            ← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective R' S),
            forall_and, hr, or_imp, Finset.mem_smul_finset]
        refine ⟨fun i ↦ ?_, fun a has ↦ ?_⟩
        · convert! isIntegral_algebraMap (x := MvPolynomial.X i)
          simp [RingHom.algebraMap_toAlgebra, f', MvPolynomial.finSuccEquiv,
            MvPolynomial.optionEquivLeft]
        · rw [← Nat.sub_add_cancel (s.le_sup has), pow_add, mul_assoc]
          exact (hr.pow _).mul (hm _)
      · refine .of_comp_finiteType (f := algebraMap R _) ?_
        rw [AlgHom.toRingHom_eq_coe, φ.comp_algebraMap, RingHom.finiteType_algebraMap]
        exact ⟨(Subalgebra.fg_top _).mpr ⟨_, rfl⟩⟩
    refine this.trans _ ⟨⟨r, hrR'⟩, hrp, ?_⟩
    suffices ⊤ ≤ R'.saturation (.powers r) (by simpa [Submonoid.powers_le]) by
      simpa [SetLike.le_def, Subalgebra.smul_def, Submonoid.mem_powers_iff,
        SetLike.ext_iff, Algebra.mem_bot] using this
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_, ⟨s.sup m, rfl⟩, Algebra.subset_adjoin ?_⟩
    simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]

end FixedUniverse

@[stacks 00Q9]
/-
**Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.** 是 Mathlib
 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.{u, v}
    {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] : ZariskisMainProperty R p := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have : Small.{u} S := small_of_surjective hf
  have := ZariskisMainProperty.of_algHom_mvPolynomial (p.comap (Shrink.algEquiv R S).toRingHom)
    ((Shrink.algEquiv R S).symm.toAlgHom.comp f)
    (.of_surjective _ <| (Shrink.algEquiv R S).symm.surjective.comp hf)
  rw [zariskisMainProperty_iff'] at this ⊢
  obtain ⟨r, hr, H⟩ := this
  refine ⟨Shrink.algEquiv R S r, hr, fun x ↦ ?_⟩
  obtain ⟨m, hm⟩ := H ((Shrink.algEquiv R S).symm x)
  exact ⟨m, by simpa [-Shrink.algEquiv_apply, -Shrink.algEquiv_symm_apply]
    using hm.map (Shrink.algEquiv R S).toAlgHom⟩

/--
The algebraic version of **Zariski's Main Theorem**:
Given a finite type `R`-algebra `S` that is quasi-finite at a prime `p`,
there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.
-/
@[stacks 00Q9]
/-
**Algebra.ZariskisMainProperty.of_finiteType.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebraic version of **Zariski's Main Theorem**:
Given a finite type `R`-algebra `S` that is quasi-finite at a prime `p`,
there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` 
is the integral
closure of `R` in `S`.
-/
lemma ZariskisMainProperty.of_finiteType.{u, v} {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p] : ZariskisMainProperty R p :=
  .of_finiteType_of_weaklyQuasiFiniteAt _

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.ZariskisMainProperty`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S),   Algebra.Zaris
kisMainProperty R p →     ∃ S', (Subalgebra.toSubmodule S').FG ∧ ∃ r, ↑r ∉ p ∧ F
unction.Bijective ⇑(Localization.awayMap S'.val.toRingHom r)
参数：p : Ideal S；Subalgebra.toSubmodule S'；Localization.awayMap S'.val.toRingHom r
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsLocalization.map_injective_of_injective`：map_injective_of_injective (h
 : Function.Injective g) [IsLocalization (M.map g) Q] : Function.Injective (map 
Q g M.le_comap_map : S -> Q)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsLocalization.Away.instMapRingHomPowersOfCoe`：∀ {A : Type u_5} [inst : 
CommSemiring A] {B : Type u_6} [inst_1 : CommSemiring B] (Bₚ : Type u_8)   [inst
_2 : CommSemiring Bₚ] [inst_3 : Alg…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Subalgebra.map_le`：map_le {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Sub
algebra R B} : map f S <= U ↔ S <= comap f U
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subalgebra.coe_comap`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring
 B] [inst_…
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
（共 56 条，此处仅展示前 30 条）
-/
lemma ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
    [Algebra.FiniteType R S] (p : Ideal S) (H : ZariskisMainProperty R p) :
    ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x ∈ s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x ↦ r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range ≤
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top, ← hs, Subalgebra.map_le, Algebra.adjoin_le_iff]
    intro x hx
    suffices ∃ a ∈ Algebra.adjoin R t, ∃ n, r ^ n ∈ Algebra.adjoin R t ∧
        ∃ k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]
/-
**Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective** 是 Ma
thlib 中的一个定理，位于命名空间 `Algebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S) [inst_4 : p.IsPr
ime] [Algebra.WeaklyQuasiFiniteAt R p],   ∃ S', (Subalgebra.toSubmodule S').FG ∧
 ∃ r, ↑r ∉ p ∧ Function.Bijective ⇑(Localization.awayMap S'.val.toRingHom r)
参数：p : Ideal S；Subalgebra.toSubmodule S'；Localization.awayMap S'.val.toRingHom r
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bij
ective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S
] [inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S),  …
· 使用定理 `Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt`：∀ {R 
: Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S] [Algebra.FiniteType R S]   (p : Ideal S) [inst_…
-/
lemma QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] :
    ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) :=
  ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective _
    (.of_finiteType_of_weaklyQuasiFiniteAt _)
/-
**Algebra.ZariskisMainProperty.quasiFiniteAt** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
ZariskisMainProperty`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S) [inst_4 : p.IsPr
ime],   Algebra.ZariskisMainProperty R p → Algebra.QuasiFiniteAt R p
参数：p : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bij
ective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S
] [inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S),  …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
· 使用引理 `Algebra.QuasiFinite.trans`：trans [QuasiFinite R S] [QuasiFinite S T] : Q
uasiFinite R T
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用引理 `Algebra.QuasiFinite.of_forall_exists_mul_mem_range`：of_forall_exists_mul
_mem_range [QuasiFinite R S] (f : S ->ₐ[R] T) (H : forall x : T, exists s : S, I
sUnit (f s) ∧ x * f s in f.range) : Quas…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.mk'_spec_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ZariskisMainProperty.quasiFiniteAt
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] (H : ZariskisMainProperty R p) :
    Algebra.QuasiFiniteAt R p := by
  obtain ⟨S', hS', r, hrp, H⟩ := H.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans _ S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 →ₐ[S] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _) <|
      IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩
/-
**Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S) [inst_4 : p.IsPr
ime] [Algebra.WeaklyQuasiFiniteAt R p],   Algebra.QuasiFiniteAt R p
参数：p : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.ZariskisMainProperty.quasiFiniteAt`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.
FiniteType R S] (p : Ideal S) [i…
· 使用定理 `Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt`：∀ {R 
: Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S] [Algebra.FiniteType R S]   (p : Ideal S) [inst_…
-/
lemma QuasiFiniteAt.of_weaklyQuasiFiniteAt
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] :
    Algebra.QuasiFiniteAt R p :=
  ZariskisMainProperty.quasiFiniteAt _ (.of_finiteType_of_weaklyQuasiFiniteAt _)
/-
**Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal R) (q : Ideal S) [i
nst_4 : q.IsPrime] [inst_5 : p.IsPrime] [q.LiesOver p]   (Q : Ideal (p.Fiber S))
 [inst_7 : Q.IsPrime],   Ideal.comap Algebra.TensorProduct.includeRight.toRingHo
m Q = q →     ∀ [Algebra.QuasiFiniteAt p.ResidueField Q], Algebra.QuasiFiniteAt 
R q
参数：p : Ideal R；q : Ideal S；Q : Ideal (p.Fiber S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField`：of_quasiFinit
eAt_residueField [p.IsPrime] [q.LiesOver p] (Q : Ideal (p.Fiber S)) [Q.IsPrime] 
(hQ : Q.comap Algebra.TensorProduct.includeRigh…
· 使用定理 `Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebr
a.FiniteType R S] (p : Ideal S) [i…
-/
lemma QuasiFiniteAt.of_quasiFiniteAt_residueField
    [FiniteType R S] (p : Ideal R) (q : Ideal S) [q.IsPrime]
    [p.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    [Algebra.QuasiFiniteAt p.ResidueField Q] :
    Algebra.QuasiFiniteAt R q :=
  have : Algebra.WeaklyQuasiFiniteAt R q := .of_quasiFiniteAt_residueField p q Q hQ
  .of_weaklyQuasiFiniteAt _
/-
**Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S] (q : PrimeSpectrum S), IsOpen 
{⟨q, ⋯⟩} → Algebra.QuasiFiniteAt R q.asIdeal
参数：q : PrimeSpectrum S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.QuasiFiniteAt.of_isOpen_singleton`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsArtinianR
ing R]   (p : PrimeSpectrum S) …
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
· 使用定理 `Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField`：∀ {R : Type u_1} {S
 : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   
[Algebra.FiniteType R S] (p : Ideal R) (q…
· 使用定理 `PrimeSpectrum.instLiesOverAsIdealComapAlgebraMap`：∀ {R : Type u} {S : Ty
pe v} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]  
 (p : PrimeSpectrum S), p.asIdeal.Lies…
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
-/
lemma QuasiFiniteAt.of_isOpen_singleton_fiber
    [FiniteType R S] (q : PrimeSpectrum S)
    (H : IsOpen (X := .comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩}) :
    Algebra.QuasiFiniteAt R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    .of_quasiFiniteAt_residueField _ q.asIdeal (e ⟨q, rfl⟩).asIdeal
      congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal)
  refine .of_isOpen_singleton _ ?_
  rwa [← Set.image_singleton, e.isOpen_image]
/-
**Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra`。
形式化陈述：quasiFiniteAt_iff_isOpen_singleton_fiber [FiniteType R S] (q : PrimeSpectr
um S) : Algebra.QuasiFiniteAt R q.asIdeal ↔ IsOpen (X
参数：q : PrimeSpectrum S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.QuasiFiniteAt.baseChange`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal S)   [inst
_3 : p.IsPrime] [Algeb…
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Algebra.QuasiFiniteAt.isClopen_singleton`：∀ {R : Type u_1} {S : Type u_2
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : PrimeSpe
ctrum S)   [IsArtinianRing R] …
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Alg
ebra.FiniteType R S] (q : PrimeSpectr…
-/
lemma quasiFiniteAt_iff_isOpen_singleton_fiber
    [FiniteType R S] (q : PrimeSpectrum S) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      IsOpen (X := .comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩} := by
  refine ⟨fun H ↦ ?_, .of_isOpen_singleton_fiber q⟩
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image, Set.image_singleton]
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    (QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) _).isOpen
  exact .baseChange q.asIdeal _ congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal).symm

end Algebra

