/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Support

/-!

# Associated primes of localized module

This file mainly proves the relation between `Ass(S⁻¹M)` and `Ass(M)`

## Main Results

* `associatedPrimes.mem_associatePrimes_of_comap_mem_associatePrimes_isLocalizedModule` :
  for an `R` module `M`, if `p` is a prime ideal of `S⁻¹R` and `p ∩ R ∈ Ass(M)` then
  `p ∈ Ass (S⁻¹M)`.

-/

public section

variable {R : Type*} [CommRing R] (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
  [hSR' : IsLocalization S R']

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f] [Module R' M'] [IsScalarTower R R' M']

open IsLocalRing LinearMap Submodule

namespace Module.associatedPrimes

include S f in
@[stacks 0310 "(1)"]
/-
**Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_
isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 `Module.associatedPrimes`。
形式化陈述：mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule (p
 : Ideal R') (ass : p.comap (algebraMap R R') in associatedPrimes R M) : p in as
sociatedPrimes R' M'
参数：p : Ideal R'；ass : p.comap (algebraMap R R') in associatedPrimes R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `IsLocalization.disjoint_under_iff`：disjoint_under_iff (J : Ideal S) : Di
sjoint (M : Set R) (J.under R) ↔ J != ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalizedModule.mk'_smul_mk'`：∀ {R : Type u_1} [inst : CommSemiring R]
 {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [
inst_2 : AddCommMono…
· 使用定理 `IsLocalizedModule.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring 
R] {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
（共 54 条，此处仅展示前 30 条）
-/
lemma mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    (p : Ideal R') (ass : p.comap (algebraMap R R') ∈ associatedPrimes R M) :
    p ∈ associatedPrimes R' M' := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · refine (IsLocalization.isPrime_iff_isPrime_disjoint S _ _).mpr
      ⟨hp, (IsLocalization.disjoint_under_iff S R' p).mpr ?_⟩
    by_contra eqtop
    simp [eqtop, Ideal.comap_top, Ideal.isPrime_iff] at hp
  · use f x
    ext t
    rcases IsLocalization.exists_mk'_eq S t with ⟨r, s, hrs⟩
    simp_rw [← hrs, Ideal.mem_radical_iff, mem_colon_singleton, ← IsLocalizedModule.mk'_one S f,
      ← IsLocalization.mk'_pow, IsLocalizedModule.mk'_smul_mk', mul_one, mem_bot,
      IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h ↦ exists_comm.mp ⟨1, ?_⟩, fun ⟨n, t, ht⟩ ↦ ?_⟩
    · simp only [← mem_colon_singleton, one_smul, ← mem_bot R, ← hx, ← Ideal.mem_radical_iff]
      exact hSR'.mk'_mem_iff.mp h
    · have : hSR'.mk' R' r s = hSR'.mk' R' (t.1 * r) 1 * hSR'.mk' R' 1 (t * s) := by
        rw [← hSR'.mk'_mul, mul_one, one_mul, ← sub_eq_zero, ← hSR'.mk'_sub, Submonoid.coe_mul]
        simp [← mul_assoc, mul_comm r t.1, IsLocalization.mk'_zero]
      rw [this]
      apply Ideal.IsTwoSided.mul_mem_of_left
      rw [IsLocalization.mk'_one, ← Ideal.mem_comap, hx]
      rcases eq_zero_or_pos n with rfl | hn
      · exact Ideal.IsTwoSided.mul_mem_of_left _ ⟨1, by simpa using! ht⟩
      · use n
        rw [mem_colon_singleton, mul_pow, mul_smul, ← mem_colon_singleton]
        exact Ideal.pow_mem_of_mem _ (by simpa using! ht) n hn
/-
**Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes**
 是 Mathlib 中的一个引理，位于命名空间 `Module.associatedPrimes`。
形式化陈述：mem_associatedPrimes_atPrime_of_mem_associatedPrimes {p : Ideal R} [p.IsPr
ime] (ass : p in associatedPrimes R M) : maximalIdeal (Localization.AtPrime p) i
n associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
参数：ass : p in associatedPrimes R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrim
es_of_isLocalizedModule`：mem_associatedPrimes_of_comap_mem_associatedPrimes_of_i
sLocalizedModule (p : Ideal R') (ass : p.comap (algebraMap R R') in associatedPr
imes …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…
-/
lemma mem_associatedPrimes_atPrime_of_mem_associatedPrimes
    {p : Ideal R} [p.IsPrime] (ass : p ∈ associatedPrimes R M) :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
  simpa [Localization.AtPrime.under_maximalIdeal] using ass

include S f in
@[stacks 0310 "(2)"]
/-
**Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_
isLocalizedModule_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Module.associatedPrimes`。
形式化陈述：comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of
_fg (p : Ideal R') (ass : p in associatedPrimes R' M') (fg : (p.comap (algebraMa
p R R')).FG) : p.comap (algebraMap R R') in associatedPrimes R M
参数：p : Ideal R'；ass : p in associatedPrimes R' M'；fg : (p.comap (algebraMap R R'
)).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_zero_of_right`：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0)
 : a • b = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring 
R] {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `IsLocalizedModule.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 42 条，此处仅展示前 30 条）
-/
lemma comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg (p : Ideal R')
    (ass : p ∈ associatedPrimes R' M') (fg : (p.comap (algebraMap R R')).FG) :
    p.comap (algebraMap R R') ∈ associatedPrimes R M := by
  rcases ass with ⟨hp, x, hx⟩
  rcases fg with ⟨T, hT⟩
  rcases IsLocalizedModule.mk'_surjective S f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R R' a ∈ p := by
    simpa [← Ideal.mem_comap, ← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, ← map_pow, algebraMap_smul,
    ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero' f] at mem
  choose e g hg using mem
  refine ⟨.under R p, (∏ a, g a).1 • m, le_antisymm ?_ fun r hr ↦ ?_⟩
  · rw [← hT, Ideal.span_le]
    intro a ha
    simp only [SetLike.mem_coe, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
      apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
    use e ⟨a, ha⟩
    rw [hu, Submonoid.coe_mul, smul_smul, ← mul_assoc, mul_comm, ← smul_smul, mul_comm, ← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · simp only [Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, smul_smul] at hr
    obtain ⟨k, hk⟩ := hr
    have mem : r ^ k * (∏ a, g a).1 ∈ Ideal.comap (algebraMap R R') p := by
      rw [hx]
      use 1
      simp_rw [pow_one, mem_colon_singleton, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
        hk, IsLocalizedModule.mk'_zero, mem_bot]
    apply hp.mem_of_pow_mem k
    rw [← map_pow]
    exact ((hp.under R).mul_mem_iff_mem_or_mem.mp mem).resolve_right
      (Set.disjoint_left.mp ((IsLocalization.disjoint_under_iff S R' p).mpr hp.1) (∏ a, g a).2)

variable (R')

include S f in
open Set in
@[stacks 0310 "(3)"]
/-
**Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of
_isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 `Module.associatedPrimes`。
形式化陈述：preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule [
IsNoetherianRing R] : (Ideal.comap (algebraMap R R')) ⁻¹' (associatedPrimes R M)
 = associatedPrimes R' M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrim
es_of_isLocalizedModule`：mem_associatedPrimes_of_comap_mem_associatedPrimes_of_i
sLocalizedModule (p : Ideal R') (ass : p.comap (algebraMap R R') in associatedPr
imes …
· 使用引理 `Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrim
es_of_isLocalizedModule_of_fg`：comap_mem_associatedPrimes_of_mem_associatedPrime
s_of_isLocalizedModule_of_fg (p : Ideal R') (ass : p in associatedPrimes R' M') 
(fg : (p.co…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isNoetherianRing_iff_ideal_fg`：isNoetherianRing_iff_ideal_fg (R : Type*)
 [Semiring R] : IsNoetherianRing R ↔ forall I : Ideal R, I.FG
-/
lemma preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    [IsNoetherianRing R] :
    (Ideal.comap (algebraMap R R')) ⁻¹' (associatedPrimes R M) = associatedPrimes R' M' := by
  ext p
  exact ⟨mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule S f p,
    fun h ↦ comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg S f p h
    ((isNoetherianRing_iff_ideal_fg R).mp ‹_› _)⟩

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-
**Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes** 是 
Mathlib 中的一个引理，位于命名空间 `Module.associatedPrimes`。
形式化陈述：minimalPrimes_annihilator_subset_associatedPrimes [IsNoetherianRing R] [Mo
dule.Finite R M] : (Module.annihilator R M).minimalPrimes subseteq associatedPri
mes R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.mem_support_iff`：Module.mem_support_iff : p in Module.support R M
 ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `associatedPrimes.nonempty`：associatedPrimes.nonempty [IsNoetherianRing R
] [Nontrivial M] : (associatedPrimes R M).Nonempty
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `IsAssociatedPrime.isPrime`：IsAssociatedPrime.isPrime (h : IsAssociatedPr
ime I M) : I.IsPrime
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Submodule.annihilator_top`：annihilator_top : (⊤ : Submodule R M).annihil
ator = Module.annihilator R M
· 使用定理 `IsAssociatedPrime.annihilator_le`：IsAssociatedPrime.annihilator_le (h : 
IsAssociatedPrime I M) : (⊤ : Submodule R M).annihilator <= I
· 使用引理 `Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPri
mes_of_isLocalizedModule`：preimage_comap_associatedPrimes_eq_associatedPrimes_of
_isLocalizedModule [IsNoetherianRing R] : (Ideal.comap (algebraMap R R')) ⁻¹' (a
ssocia…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.disjoint_under_iff`：disjoint_under_iff (J : Ideal S) : Di
sjoint (M : Set R) (J.under R) ↔ J != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Minimal.eq_of_le`：Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : 
y <= x) : y = x
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
-/
lemma minimalPrimes_annihilator_subset_associatedPrimes [IsNoetherianRing R] [Module.Finite R M] :
    (Module.annihilator R M).minimalPrimes ⊆ associatedPrimes R M := by
  intro p hp
  have prime := hp.isPrime
  let Rₚ := Localization.AtPrime p
  have : Nontrivial (LocalizedModule p.primeCompl M) := by
    simpa [← Module.mem_support_iff (p := ⟨p, prime⟩), Module.support_eq_zeroLocus] using! hp.1.2
  rcases associatedPrimes.nonempty Rₚ (LocalizedModule p.primeCompl M) with ⟨q, hq⟩
  have q_prime : q.IsPrime := IsAssociatedPrime.isPrime hq
  simp only [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule p.primeCompl
    Rₚ (LocalizedModule.mkLinearMap p.primeCompl M), Set.mem_preimage] at hq
  have ann_le : Module.annihilator R M ≤ Ideal.comap (algebraMap R Rₚ) q :=
    le_of_eq_of_le Submodule.annihilator_top.symm (IsAssociatedPrime.annihilator_le hq)
  have le : Ideal.comap (algebraMap R Rₚ) q ≤ p := by
    have := (IsLocalization.disjoint_under_iff p.primeCompl Rₚ q).mpr q_prime.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! this
  simpa [Minimal.eq_of_le hp.out ⟨IsAssociatedPrime.isPrime hq, ann_le⟩ le] using! hq

end Module.associatedPrimes

