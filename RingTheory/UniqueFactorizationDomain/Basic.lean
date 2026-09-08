/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.ENat.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic results on unique factorization monoids

## Main results
* `prime_factors_unique`: the prime factors of an element in a cancellative
  commutative monoid with zero (e.g. an integral domain) are unique up to associates
* `UniqueFactorizationMonoid.factors_unique`: the irreducible factors of an element
  in a unique factorization monoid (e.g. a UFD) are unique up to associates
* `UniqueFactorizationMonoid.iff_exists_prime_factors`: unique factorization exists iff each nonzero
  elements factors into a product of primes
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
* `UniqueFactorizationMonoid.exists_reduced_factors`: in a UFM, we can divide out a common factor
  to get relatively prime elements.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

/-
**WfDvdMonoid.of_wfDvdMonoid_associates** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdMonoid`。
形式化陈述：of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α
参数：_ : WfDvdMonoid (Associates α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.wellFounded_iff`：Function.Surjective.wellFounded_iff
 {f : α -> β} (hf : Surjective f) (o : forall {a b}, r a b ↔ s (f a) (f b)) : We
llFounded r ↔ WellFounded…
· 使用定理 `Associates.mk_surjective`：mk_surjective [Monoid M] : Function.Surjective
 (@Associates.mk M _)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Associates.mk_dvdNotUnit_mk_iff`：mk_dvdNotUnit_mk_iff {a b : M} : DvdNot
Unit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
-/
theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

variable [WfDvdMonoid α]
/-
**WfDvdMonoid.wfDvdMonoid_associates** 是 Mathlib 中的一个实例，位于命名空间 `WfDvdMonoid`。
形式化陈述：wfDvdMonoid_associates : WfDvdMonoid (Associates α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.wellFounded_iff`：Function.Surjective.wellFounded_iff
 {f : α -> β} (hf : Surjective f) (o : forall {a b}, r a b ↔ s (f a) (f b)) : We
llFounded r ↔ WellFounded…
· 使用定理 `Associates.mk_surjective`：mk_surjective [Monoid M] : Function.Surjective
 (@Associates.mk M _)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Associates.mk_dvdNotUnit_mk_iff`：mk_dvdNotUnit_mk_iff {a b : M} : DvdNot
Unit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
-/
instance wfDvdMonoid_associates : WfDvdMonoid (Associates α) :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩
/-
**WfDvdMonoid.wellFoundedLT_associates** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdMonoid`。
形式化陈述：wellFoundedLT_associates : WellFoundedLT (Associates α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Associates.dvdNotUnit_of_lt`：dvdNotUnit_of_lt {a b : Associates M} (hlt 
: a < b) : DvdNotUnit a b
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
-/
theorem wellFoundedLT_associates : WellFoundedLT (Associates α) :=
  ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

end WfDvdMonoid

/-
**WfDvdMonoid.of_wellFoundedLT_associates** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WfDvdMonoid.of_wellFoundedLT_associates [CommMonoidWithZero α] [IsCancelMu
lZero α] (h : WellFoundedLT (Associates α)) : WfDvdMonoid α
参数：h : WellFoundedLT (Associates α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.of_wfDvdMonoid_associates`：of_wfDvdMonoid_associates (_ : Wf
DvdMonoid (Associates α)) : WfDvdMonoid α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Associates.dvdNotUnit_iff_lt`：dvdNotUnit_iff_lt {a b : Associates M} : D
vdNotUnit a b ↔ a < b
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem WfDvdMonoid.of_wellFoundedLT_associates [CommMonoidWithZero α] [IsCancelMulZero α]
    (h : WellFoundedLT (Associates α)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by convert h.wf; exact Associates.dvdNotUnit_iff_lt⟩
/-
**WfDvdMonoid.iff_wellFounded_associates** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WfDvdMonoid.iff_wellFounded_associates [CommMonoidWithZero α] [IsCancelMul
Zero α] : WfDvdMonoid α ↔ WellFoundedLT (Associates α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.wellFoundedLT_associates`：wellFoundedLT_associates : WellFou
ndedLT (Associates α)
· 使用定理 `WfDvdMonoid.of_wellFoundedLT_associates`：WfDvdMonoid.of_wellFoundedLT_as
sociates [CommMonoidWithZero α] [IsCancelMulZero α] (h : WellFoundedLT (Associat
es α)) : WfDvdMonoid α
-/
theorem WfDvdMonoid.iff_wellFounded_associates [CommMonoidWithZero α] [IsCancelMulZero α] :
    WfDvdMonoid α ↔ WellFoundedLT (Associates α) :=
  ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩
/-
**Associates.ufm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Associates.ufm [CommMonoidWithZero α] [UniqueFactorizationMonoid α] : Uniq
ueFactorizationMonoid (Associates α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.irreducible_iff_prime_iff`：irreducible_iff_prime_iff : (foral
l a : M, Irreducible a ↔ Prime a) ↔ forall a : Associates M, Irreducible a ↔ Pri
me a
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
-/
instance Associates.ufm [CommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }
/-
**prime_factors_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_factors_unique [CommMonoidWithZero α] [IsCancelMulZero α] : forall {
f g : Multiset α}, (forall x in f, Prime x) -> (forall x in g, Prime x) -> f.pro
d ~ᵤ g.prod -> Multiset.Rel Associated f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_zero_left`：rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b =
 0
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `exists_associated_mem_of_dvd_prod`：exists_associated_mem_of_dvd_prod [Co
mmMonoidWithZero M₀] [IsCancelMulZero M₀] {p : M₀} (hp : Prime p) {s : Multiset 
M₀} : (forall r in s, P…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Multiset.mem_of_mem_erase`：mem_of_mem_erase {a b : α} {s : Multiset α} :
 a in s.erase b -> a in s
· 使用定理 `Associated.of_mul_left`：Associated.of_mul_left [CommMonoidWithZero M] [I
sCancelMulZero M] {a b c d : M} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a != 0)
 : b ~ᵤ d
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
-/
theorem prime_factors_unique [CommMonoidWithZero α] [IsCancelMulZero α] :
    ∀ {f g : Multiset α},
      (∀ x ∈ f, Prime x) → (∀ x ∈ g, Prime x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g := by
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
    exact Multiset.rel_zero_left.2 <|
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
        (hg x hx).not_isUnit <|
          isUnit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  | cons p f ih =>
    intro g hf hg hfg
    let ⟨b, hbg, hb⟩ :=
      (exists_associated_mem_of_dvd_prod (hf p (by simp)) fun q hq => hg _ hq) <|
        hfg.dvd_iff_dvd_right.1 (show p ∣ (p ::ₘ f).prod by simp)
    have := Classical.decEq α
    rw [← Multiset.cons_erase hbg]
    exact
      Multiset.Rel.cons hb
        (ih (fun q hq => hf _ (by simp [hq]))
          (fun {q} (hq : q ∈ g.erase b) => hg q (Multiset.mem_of_mem_erase hq))
          (Associated.of_mul_left
            (by rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg]) hb
            (hf p (by simp)).ne_zero))

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/-
**UniqueFactorizationMonoid.factors_unique** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFact
orizationMonoid`。
形式化陈述：factors_unique {f g : Multiset α} (hf : forall x in f, Irreducible x) (hg 
: forall x in g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated
 f g
参数：hf : forall x in f, Irreducible x；hg : forall x in g, Irreducible x；h : f.pro
d ~ᵤ g.prod。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prime_factors_unique`：prime_factors_unique [CommMonoidWithZero α] [IsCan
celMulZero α] : forall {f g : Multiset α}, (forall x in f, Prime x) -> (forall x
 in g, Pri…
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
-/
theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h
/-
**UniqueFactorizationMonoid._root_.Associated.card_factors_eq** 是 Mathlib 中的一个定理
，位于命名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.card_factors_eq {a b : α} (h : Associated a b) :
    (factors a).card = (factors b).card := by
  by_cases hb : b = 0
  · simp_all
  have ha : a ≠ 0 := h.ne_zero_iff.mpr hb
  apply Multiset.card_eq_card_of_rel
  apply factors_unique irreducible_of_factor irreducible_of_factor
  exact (factors_prod ha).trans <| h.trans (factors_prod hb).symm

end UniqueFactorizationMonoid

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
/-
**prime_factors_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_factors_irreducible [CommMonoidWithZero α] {a : α} {f : Multiset α} 
(ha : Irreducible a) (pfa : (forall b in f, Prime b) ∧ f.prod ~ᵤ a) : exists p, 
a ~ᵤ p ∧ f = {p}
参数：ha : Irreducible a；pfa : (forall b in f, Prime b) ∧ f.prod ~ᵤ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors.
-/
theorem prime_factors_irreducible [CommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  have := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) → (∀ b ∈ g, Prime b) → ∃ p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hs0
      apply (hs q (by simp [hq])).2.1
      refine (ha.isUnit_or_isUnit (?_ : _ = p * ↑u * (s.erase q).prod * _)).resolve_left ?_
      · rw [mul_right_comm _ _ q, mul_assoc, ← Multiset.prod_cons, Multiset.cons_erase hq, ← hu,
          mul_comm, mul_comm p _, mul_assoc]
        simp
      apply mt isUnit_of_mul_isUnit_left (mt isUnit_of_mul_isUnit_left _)
      apply (hs p (Multiset.mem_cons_self _ _)).2.1
    simp only [mul_one, Multiset.prod_cons, Multiset.prod_zero, hs0] at *
    exact ⟨Associated.symm ⟨u, hu⟩, rfl⟩
/-
**irreducible_iff_prime_of_existsUnique_irreducible_factors** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：irreducible_iff_prime_of_existsUnique_irreducible_factors [CommMonoidWithZ
ero α] [IsCancelMulZero α] (eif : forall a : α, a != 0 -> exists f : Multiset α,
 (forall b in f, Irreducible b) ∧ f.prod ~ᵤ a) (uif : forall f g : Multiset α, (
forall x in f, Irreducible x) -> (forall x in g, Irreducible x) -> f.prod ~ᵤ g.p
rod -> Multiset.Rel Associated f g) (p : α) : Irreducible p ↔ Prime p
参数：eif : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Irreduci
ble b) ∧ f.prod ~ᵤ a；uif : forall f g : Multiset α, (forall x in f, Irreducible 
x) -> (forall x in g, Irreducible x) -> f.prod ~ᵤ g.prod -> Multiset.Rel Associa
ted f g；p : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Associated.mul_mul`：Associated.mul_mul [CommMonoid M] {a₁ a₂ b₁ b₂ : M} 
(h₁ : a₁ ~ᵤ b₁) (h₂ : a₂ ~ᵤ b₂) : a₁ * a₂ ~ᵤ b₁ * b₂
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Multiset.exists_mem_of_rel_of_mem`：exists_mem_of_rel_of_mem {r : α -> β 
-> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) : forall {a : α}, a i
n s -> exists b in t, r…
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
（共 35 条，此处仅展示前 30 条）
-/
theorem irreducible_iff_prime_of_existsUnique_irreducible_factors [CommMonoidWithZero α]
    [IsCancelMulZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀ x ∈ f, Irreducible x) →
          (∀ x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g)
    (p : α) : Irreducible p ↔ Prime p :=
  letI := Classical.decEq α
  ⟨ fun hpi =>
    ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
      if hab0 : a * b = 0 then
        (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (fun ha0 => by simp [ha0]) fun hb0 => by
          simp [hb0]
      else by
        have hx0 : x ≠ 0 := fun hx0 => by simp_all
        have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
        have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
        obtain ⟨fx, hfx⟩ := eif x hx0
        obtain ⟨fa, hfa⟩ := eif a ha0
        obtain ⟨fb, hfb⟩ := eif b hb0
        have h : Multiset.Rel Associated (p ::ₘ fx) (fa + fb) := by
          apply uif
          · exact fun i hi => (Multiset.mem_cons.1 hi).elim (fun hip => hip.symm ▸ hpi) (hfx.1 _)
          · exact fun i hi => (Multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _)
          calc
            Multiset.prod (p ::ₘ fx) ~ᵤ a * b := by
              rw [hx, Multiset.prod_cons]; exact hfx.2.mul_left _
            _ ~ᵤ fa.prod * fb.prod := hfa.2.symm.mul_mul hfb.2.symm
            _ = _ := by rw [Multiset.prod_add]
        exact
          let ⟨q, hqf, hq⟩ := Multiset.exists_mem_of_rel_of_mem h (Multiset.mem_cons_self p _)
          (Multiset.mem_add.1 hqf).elim
            (fun hqa =>
              Or.inl <| hq.dvd_iff_dvd_left.2 <| hfa.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqa))
            fun hqb =>
            Or.inr <| hq.dvd_iff_dvd_left.2 <| hfb.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqb)⟩,
    Prime.irreducible⟩

namespace UniqueFactorizationMonoid

open Multiset

variable [CommMonoidWithZero α]
variable [UniqueFactorizationMonoid α]

@[simp]
/-
**UniqueFactorizationMonoid.factors_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：factors_one : factors (1 : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_zero_right`：rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a
 = 0
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using factors
  rw [← rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (notMem_zero x hx).elim) ?_
  rw [prod_zero]
  exact factors_prod one_ne_zero
/-
**UniqueFactorizationMonoid.exists_mem_factors_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：exists_mem_factors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : 
p ∣ a -> exists q in factors a, p ~ᵤ q
参数：ha0 : a != 0；hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `Multiset.exists_mem_of_rel_of_mem`：exists_mem_of_rel_of_mem {r : α -> β 
-> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) : forall {a : α}, a i
n s -> exists b in t, r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ factors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun _ hx => (mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
          prod (factors a) ~ᵤ a := factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ prod (p ::ₘ factors b) := by
            rw [prod_cons]; exact (factors_prod hb0).symm.mul_left _)
  exists_mem_of_rel_of_mem this (by simp)
/-
**UniqueFactorizationMonoid.exists_mem_factors** 是 Mathlib 中的一个定理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：exists_mem_factors {x : α} (hx : x != 0) (h : ¬IsUnit x) : exists p, p in 
factors x
参数：hx : x != 0；h : ¬IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `UniqueFactorizationMonoid.exists_mem_factors_of_dvd`：exists_mem_factors_
of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a -> exists q in fact
ors a, p ~ᵤ q
-/
theorem exists_mem_factors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) : ∃ p, p ∈ factors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩
/-
**UniqueFactorizationMonoid.factors_eq_singleton_of_irreducible** 是 Mathlib 中的一个
定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：factors_eq_singleton_of_irreducible {a : α} (ha : Irreducible a) : exists 
b, Associated a b ∧ factors a = {b}
参数：ha : Irreducible a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.exists_mem_factors_of_dvd`：exists_mem_factors_
of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a -> exists q in fact
ors a, p ~ᵤ q
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.singleton_le`：singleton_le {a : α} {s : Multiset α} : {a} <= s 
↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.card_factors_of_irreducible`：card_factors_of_i
rreducible {a : α} (ha : Irreducible a) : (factors a).card = 1
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem factors_eq_singleton_of_irreducible {a : α} (ha : Irreducible a) :
    ∃ b, Associated a b ∧ factors a = {b} := by
  obtain ⟨b, hbmem, hab⟩ := exists_mem_factors_of_dvd ha.ne_zero ha dvd_rfl
  exact ⟨b, hab, .symm <| Multiset.eq_of_le_of_card_le (Multiset.singleton_le.mpr hbmem)
    (by rw [card_factors_of_irreducible ha, Multiset.card_singleton])⟩
/-
**UniqueFactorizationMonoid.factors_mul** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：factors_mul {x y : α} (hx : x != 0) (hy : y != 0) : Rel Associated (factor
s (x * y)) (factors x + factors y)
参数：hx : x != 0；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Associated.mul_mul`：Associated.mul_mul [CommMonoid M] {a₁ a₂ b₁ b₂ : M} 
(h₁ : a₁ ~ᵤ b₁) (h₂ : a₂ ~ᵤ b₂) : a₁ * a₂ ~ᵤ b₁ * b₂
-/
theorem factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    Rel Associated (factors (x * y)) (factors x + factors y) := by
  classical
  refine
    factors_unique irreducible_of_factor
      (fun a ha =>
        (mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans ?_)
  rw [prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy)).symm
/-
**UniqueFactorizationMonoid.factors_pow** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：factors_pow {x : α} (n : Nat) : Rel Associated (factors (x ^ n)) (n • fact
ors x)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factors_pow {x : α} (n : ℕ) :
    Rel Associated (factors (x ^ n)) (n • factors x) := by
  match n with
  | 0 => rw [zero_nsmul, pow_zero, factors_one, rel_zero_right]
  | n + 1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
      refine Rel.add ?_ <| factors_pow n
      exact rel_refl_of_refl_on fun y _ => Associated.refl _
/-
**UniqueFactorizationMonoid.factors_pow_count_prod** 是 Mathlib 中的一个定理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：factors_pow_count_prod [DecidableEq α] {x : α} (hx : x != 0) : (∏ p in (fa
ctors x).toFinset, p ^ (factors x).count p) ~ᵤ x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_sum`：prod_sum {ι : Type*} [CommMonoid M] (f : ι -> Multise
t M) (s : Finset ι) : (∑ x in s, f x).prod = ∏ x in s, (f x).prod
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Multiset.prod_nsmul`：∀ {M : Type u_5} [inst : CommMonoid M] (m : Multise
t M) (n : ℕ), (n • m).prod = m.prod ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.toFinset_sum_count_nsmul_eq`：toFinset_sum_count_nsmul_eq (s : M
ultiset ι) : ∑ a in s.toFinset, s.count a • {a} = s
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
-/
theorem factors_pow_count_prod [DecidableEq α] {x : α} (hx : x ≠ 0) :
    (∏ p ∈ (factors x).toFinset, p ^ (factors x).count p) ~ᵤ x :=
  calc
  _ = prod (∑ a ∈ toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx
/-
**UniqueFactorizationMonoid.factors_rel_of_associated** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：factors_rel_of_associated {a b : α} (h : Associated a b) : Rel Associated 
(factors a) (factors b)
参数：h : Associated a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_iff_and_or_not_and_not`：iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b
 ∨ ¬a ∧ ¬b
· 使用定理 `Associated.eq_zero_iff`：Associated.eq_zero_iff [MonoidWithZero M] {a b :
 M} (h : a ~ᵤ b) : a = 0 ↔ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.factors_zero`：factors_zero : factors (0 : α) =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
-/
theorem factors_rel_of_associated {a b : α} (h : Associated a b) :
    Rel Associated (factors a) (factors b) := by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm
/-
**UniqueFactorizationMonoid.factors_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：factors_of_isUnit {x : α} (hx : IsUnit x) : factors x = 0
参数：hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.factors_one`：factors_one : factors (1 : α) = 0
· 使用定理 `UniqueFactorizationMonoid.factors_rel_of_associated`：factors_rel_of_asso
ciated {a b : α} (h : Associated a b) : Rel Associated (factors a) (factors b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
-/
theorem factors_of_isUnit {x : α} (hx : IsUnit x) : factors x = 0 := by
  simpa using factors_rel_of_associated (associated_one_iff_isUnit.mpr hx)

@[simp]
/-
**UniqueFactorizationMonoid.factors_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：factors_eq_zero {x : α} (hx : x != 0) : factors x = 0 ↔ IsUnit x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniqueFactorizationMonoid.exists_mem_factors`：exists_mem_factors {x : α}
 (hx : x != 0) (h : ¬IsUnit x) : exists p, p in factors x
· 使用定理 `UniqueFactorizationMonoid.factors_of_isUnit`：factors_of_isUnit {x : α} (
hx : IsUnit x) : factors x = 0
-/
theorem factors_eq_zero {x : α} (hx : x ≠ 0) : factors x = 0 ↔ IsUnit x :=
  ⟨fun h ↦ by contrapose! h; simpa [eq_zero_iff_forall_notMem] using exists_mem_factors hx h,
    factors_of_isUnit⟩

@[simp]
/-
**UniqueFactorizationMonoid.factors_pos** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：factors_pos {x : α} (hx : x != 0) : 0 < factors x ↔ ¬IsUnit x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `UniqueFactorizationMonoid.factors_eq_zero`：factors_eq_zero {x : α} (hx :
 x != 0) : factors x = 0 ↔ IsUnit x
-/
theorem factors_pos {x : α} (hx : x ≠ 0) : 0 < factors x ↔ ¬IsUnit x :=
  bot_lt_iff_ne_bot.trans (not_iff_not.mpr (factors_eq_zero hx))

end UniqueFactorizationMonoid

namespace Associates

attribute [local instance] Associated.setoid

open Multiset UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

set_option backward.isDefEq.respectTransparency false in
/-
**Associates.unique'** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：unique' {p q : Multiset (Associates α)} : (forall a in p, Irreducible a) -
> (forall a in q, Irreducible a) -> p.prod = q.prod -> p = q
参数：Associates α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on_multiset_quot`：induction_on_multiset_quot {r : α -
> α -> Prop} {p : Multiset (Quot r) -> Prop} (s : Multiset (Quot r)) : (forall s
 : Multiset α, p (s.map (…
· 使用定理 `Multiset.map_mk_eq_map_mk_of_rel`：map_mk_eq_map_mk_of_rel {r : α -> α ->
 Prop} {s t : Multiset α} (hst : s.Rel r t) : s.map (Quot.mk r) = t.map (Quot.mk
 r)
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `Multiset.mem_map_of_mem`：mem_map_of_mem (f : α -> β) {a : α} {s : Multis
et α} (h : a in s) : f a in map f s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Associates.quot_mk_eq_mk`：quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Set
oid.r a = Associates.mk a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
-/
theorem unique' {p q : Multiset (Associates α)} :
    (∀ a ∈ p, Irreducible a) → (∀ a ∈ q, Irreducible a) → p.prod = q.prod → p = q := by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
  · exact fun a ha => irreducible_mk.1 <| hs _ <| Multiset.mem_map_of_mem _ ha
  · exact fun a ha => irreducible_mk.1 <| ht _ <| Multiset.mem_map_of_mem _ ha
  have eq' : (Quot.mk Setoid.r : α → Associates α) = Associates.mk := funext quot_mk_eq_mk
  rwa [eq', prod_mk, prod_mk, mk_eq_mk_iff_associated] at eq
/-
**Associates.prod_le_prod_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)} (hp : f
orall a in p, Irreducible a) (hq : forall a in q, Irreducible a) : p.prod <= q.p
rod ↔ p <= q
参数：Associates α；hp : forall a in p, Irreducible a；hq : forall a in q, Irreducibl
e a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_exists_add`：le_iff_exists_add {s t : Multiset α} : s <= 
t ↔ exists u, t = s + u
· 使用定理 `Associates.unique'`：unique' {p q : Multiset (Associates α)} : (forall a 
in p, Irreducible a) -> (forall a in q, Irreducible a) -> p.prod = q.prod -> p =
 q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `not_irreducible_zero`：not_irreducible_zero [MonoidWithZero M] : ¬Irreduc
ible (0 : M) | ⟨hn0, h⟩ => have : IsUnit (0 : M) ∨ IsUnit (0 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_eq_zero_iff`：∀ {M₀ : Type u_3} [inst : CommMonoidWithZero 
M₀] [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀},   s.prod = 0 ↔ 0 ∈ s
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Associates.instNontrivial`：∀ {M : Type u_1} [inst : MonoidWithZero M] [N
ontrivial M], Nontrivial (Associates M)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Associates.prod_le_prod`：prod_le_prod {p q : Multiset (Associates M)} (h
 : p <= q) : p.prod <= q.prod
-/
theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)}
    (hp : ∀ a ∈ p, Irreducible a) (hq : ∀ a ∈ q, Irreducible a) : p.prod ≤ q.prod ↔ p ≤ q := by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx ↦ ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq.mp (factors_prod fun hc => ?_).symm
    refine not_irreducible_zero (hq _ ?_)
    rw [← prod_eq_zero_iff, eqc, hc, mul_zero]

end Associates

section ExistsPrimeFactors

variable [CommMonoidWithZero α] [IsCancelMulZero α]
variable (pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a)
include pf

/-
**WfDvdMonoid.of_exists_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `RelHom.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r →r s) r s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.card_pos`：card_pos {s : Multiset α} : 0 < card s ↔ s != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
（共 42 条，此处仅展示前 30 条）
-/
theorem WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α :=
  ⟨by
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ : (DvdNotUnit : α → α → Prop) →r ((· < ·) : ℕ∞ → ℕ∞ → Prop)) wellFounded_lt
    · intro a
      by_cases h : a = 0
      · exact ⊤
      exact ↑(Multiset.card (Classical.choose (pf a h)))
    rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
    rw [dif_neg ane0]
    by_cases h : b = 0
    · simp [h, lt_top_iff_ne_top]
    · rw [dif_neg h, Nat.cast_lt]
      have cne0 : c ≠ 0 := by
        refine mt (fun con => ?_) h
        rw [b_eq, con, mul_zero]
      calc
        Multiset.card (Classical.choose (pf a ane0)) <
            _ + Multiset.card (Classical.choose (pf c cne0)) :=
          lt_add_of_pos_right _
            (Multiset.card_pos.mpr fun con => hc (associated_one_iff_isUnit.mp ?_))
        _ = Multiset.card (Classical.choose (pf a ane0) + Classical.choose (pf c cne0)) :=
          (Multiset.card_add _ _).symm
        _ = Multiset.card (Classical.choose (pf b h)) :=
          Multiset.card_eq_card_of_rel
          (prime_factors_unique ?_ (Classical.choose_spec (pf _ h)).1 ?_)
      · convert! (Classical.choose_spec (pf c cne0)).2.symm
        rw [con, Multiset.prod_zero]
      · intro x hadd
        rw [Multiset.mem_add] at hadd
        rcases hadd with h | h <;> apply (Classical.choose_spec (pf _ _)).1 _ h <;> assumption
      · rw [Multiset.prod_add]
        trans a * c
        · apply Associated.mul_mul <;> apply (Classical.choose_spec (pf _ _)).2 <;> assumption
        · rw [← b_eq]
          apply (Classical.choose_spec (pf _ _)).2.symm; assumption⟩
/-
**irreducible_iff_prime_of_exists_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Pr
ime p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `prime_factors_irreducible`：prime_factors_irreducible [CommMonoidWithZero
 α] {a : α} {f : Multiset α} (ha : Irreducible a) (pfa : (forall b in f, Prime b
) ∧ f.prod ~ᵤ a…
· 使用定理 `Associated.prime_iff`：Associated.prime_iff [CommMonoidWithZero M] {p q :
 M} (h : p ~ᵤ q) : Prime p ↔ Prime q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Mu
ltiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)
/-
**UniqueFactorizationMonoid.of_exists_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMon
oid α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.of_exists_prime_factors`：WfDvdMonoid.of_exists_prime_factors
 : WfDvdMonoid α
· 使用定理 `irreducible_iff_prime_of_exists_prime_factors`：irreducible_iff_prime_of_
exists_prime_factors {p : α} : Irreducible p ↔ Prime p
-/
theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

/-
**UniqueFactorizationMonoid.iff_exists_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：UniqueFactorizationMonoid.iff_exists_prime_factors [CommMonoidWithZero α] 
[IsCancelMulZero α] : UniqueFactorizationMonoid α ↔ forall a : α, a != 0 -> exis
ts f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `UniqueFactorizationMonoid.of_exists_prime_factors`：UniqueFactorizationMo
noid.of_exists_prime_factors : UniqueFactorizationMonoid α
-/
theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CommMonoidWithZero α]
    [IsCancelMulZero α] :
    UniqueFactorizationMonoid α ↔
      ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩

section

variable {β : Type*} [CommMonoidWithZero α] [CommMonoidWithZero β]

/-
**MulEquiv.uniqueFactorizationMonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.uniqueFactorizationMonoid (e : α ≃* β) (hα : UniqueFactorizationM
onoid α) : UniqueFactorizationMonoid β
参数：e : α ≃* β；hα : UniqueFactorizationMonoid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulEquiv.isCancelMulZero_iff`：isCancelMulZero_iff (e : A ≃* B) : IsCance
lMulZero A ↔ IsCancelMulZero B where mp _
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.iff_exists_prime_factors`：UniqueFactorizationM
onoid.iff_exists_prime_factors [CommMonoidWithZero α] [IsCancelMulZero α] : Uniq
ueFactorizationMonoid α ↔ forall a : α, …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquiv.prime_iff`：MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [Mu
lEquivClass E M N] (e : E) : Prime (e p) ↔ Prime p
· 使用定理 `Multiset.prod_hom`：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
 [MonoidHomClass F M N] (f : F) : (s.map f).prod = f s.prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.toMonoidHom_eq_coe`：toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoi
dHom = (f : M ->* N)
· 使用定理 `Units.coe_map`：coe_map (f : M ->* N) (x : Mˣ) : ↑(map f x) = f x
· 使用定理 `MonoidHom.coe_coe`：MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((
f : M ->* N) : M -> N) = f
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem MulEquiv.uniqueFactorizationMonoid (e : α ≃* β) (hα : UniqueFactorizationMonoid α) :
    UniqueFactorizationMonoid β := by
  have := e.isCancelMulZero_iff.mp inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
      ha <| by
        convert! ← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := Multiset.mem_map.1 hb
        he ▸ (prime_iff e).2 (hp c hc),
        Units.map e.toMonoidHom u,
      by
        rw [Multiset.prod_hom, toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, ← map_mul e, h,
          apply_symm_apply]⟩
/-
**MulEquiv.uniqueFactorizationMonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) : UniqueFactorizationM
onoid α ↔ UniqueFactorizationMonoid β
参数：e : α ≃* β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.uniqueFactorizationMonoid`：MulEquiv.uniqueFactorizationMonoid (
e : α ≃* β) (hα : UniqueFactorizationMonoid α) : UniqueFactorizationMonoid β
-/
theorem MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

end

namespace UniqueFactorizationMonoid

/-
**UniqueFactorizationMonoid.of_existsUnique_irreducible_factors** 是 Mathlib 中的一个
定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：of_existsUnique_irreducible_factors [CommMonoidWithZero α] [IsCancelMulZer
o α] (eif : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Irred
ucible b) ∧ f.prod ~ᵤ a) (uif : forall f g : Multiset α, (forall x in f, Irreduc
ible x) -> (forall x in g, Irreducible x) -> f.prod ~ᵤ g.prod -> Multiset.Rel As
sociated f g) : UniqueFactorizationMonoid α
参数：eif : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Irreduci
ble b) ∧ f.prod ~ᵤ a；uif : forall f g : Multiset α, (forall x in f, Irreducible 
x) -> (forall x in g, Irreducible x) -> f.prod ~ᵤ g.prod -> Multiset.Rel Associa
ted f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.of_exists_prime_factors`：UniqueFactorizationMo
noid.of_exists_prime_factors : UniqueFactorizationMonoid α
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irreducible_iff_prime_of_existsUnique_irreducible_factors`：irreducible_i
ff_prime_of_existsUnique_irreducible_factors [CommMonoidWithZero α] [IsCancelMul
Zero α] (eif : forall a : α, a != 0 -> exists f…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_existsUnique_irreducible_factors [CommMonoidWithZero α] [IsCancelMulZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀ x ∈ f, Irreducible x) →
          (∀ x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g) :
    UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert! eif using 7
      simp_rw [irreducible_iff_prime_of_existsUnique_irreducible_factors eif uif])

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
/-
**UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors** 是 Mathlib 中的一个定理，位
于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：isRelPrime_iff_no_prime_factors {a b : R} (ha : a != 0) : IsRelPrime a b ↔
 forall ⦃d⦄, d ∣ a -> d ∣ b -> ¬Prime d
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `WfDvdMonoid.isRelPrime_of_no_irreducible_factors`：isRelPrime_of_no_irred
ucible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z : α, Irreduc
ible z -> z ∣ x -> ¬z ∣ y) : IsRelPrim…
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
-/
theorem isRelPrime_iff_no_prime_factors {a b : R} (ha : a ≠ 0) :
    IsRelPrime a b ↔ ∀ ⦃d⦄, d ∣ a → d ∣ b → ¬Prime d :=
  ⟨fun h _ ha hb ↦ (·.not_isUnit <| h ha hb),
    fun h ↦ WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (ha ·.1) fun _ irr ha hb ↦ h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `IsCoprime.dvd_of_dvd_mul_left`. -/
/-
**UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors** 是 Mathlib 
中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a != 0) (h : for
all ⦃d⦄, d ∣ a -> d ∣ c -> ¬Prime d) : a ∣ b * c -> a ∣ b
参数：ha : a != 0；h : forall ⦃d⦄, d ∣ a -> d ∣ c -> ¬Prime d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right`：IsRelPrime.dvd_of_dvd_mul_right (H1 : I
sRelPrime x z) (H2 : x ∣ y * z) : x ∣ y
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors`：isRelPrime_if
f_no_prime_factors {a b : R} (ha : a != 0) : IsRelPrime a b ↔ forall ⦃d⦄, d ∣ a 
-> d ∣ b -> ¬Prime d

--- 原说明 ---
Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a 
∣ b`.
Compare `IsCoprime.dvd_of_dvd_mul_left`.
-/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (h : ∀ ⦃d⦄, d ∣ a → d ∣ c → ¬Prime d) : a ∣ b * c → a ∣ b :=
  ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `IsCoprime.dvd_of_dvd_mul_right`. -/
/-
**UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors** 是 Mathlib
 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a != 0) (no_fac
tors : forall {d}, d ∣ a -> d ∣ b -> ¬Prime d) : a ∣ b * c -> a ∣ c
参数：ha : a != 0；no_factors : forall {d}, d ∣ a -> d ∣ b -> ¬Prime d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`：dvd_o
f_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a != 0) (h : forall ⦃d⦄, d 
∣ a -> d ∣ c -> ¬Prime d) : a ∣ b * c -> a ∣ b

--- 原说明 ---
Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a 
∣ c`.
Compare `IsCoprime.dvd_of_dvd_mul_right`.
-/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : a ∣ b * c → a ∣ c := by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
/-
**UniqueFactorizationMonoid.exists_reduced_factors** 是 Mathlib 中的一个定理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：exists_reduced_factors : forall a != (0 : R), forall b, exists a' b' c', I
sRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.induction_on_prime`：induction_on_prime {P : α 
-> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x) (h₃ : forall a 
p : α, a != 0 -> Prime p -> P a ->…
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.left_dvd_or_dvd_right_of_dvd_mul`：Prime.left_dvd_or_dvd_right_of_d
vd_mul {p : M} (hp : Prime p) {a b : M} : a ∣ p * b -> p ∣ a ∨ a ∣ b
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)

--- 原说明 ---
If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common.
-/
theorem exists_reduced_factors :
    ∀ a ≠ (0 : R), ∀ b,
      ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b := by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcases h with ⟨b, rfl⟩
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b
      refine ⟨a', b', p * c', @no_factor, ?_, ?_⟩
      · rw [mul_assoc, ha']
      · rw [mul_assoc, hb']
    · obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b
      refine ⟨p * a', b', c', ?_, mul_left_comm _ _ _, rfl⟩
      intro q q_dvd_pa' q_dvd_b'
      rcases p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q | q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
      exact coprime q_dvd_a' q_dvd_b'
/-
**UniqueFactorizationMonoid.exists_reduced_factors'** 是 Mathlib 中的一个定理，位于命名空间 `U
niqueFactorizationMonoid`。
形式化陈述：exists_reduced_factors' (a b : R) (hb : b != 0) : exists a' b' c', IsRelPr
ime a' b' ∧ c' * a' = a ∧ c' * b' = b
参数：a b : R；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.exists_reduced_factors`：exists_reduced_factors
 : forall a != (0 : R), forall b, exists a' b' c', IsRelPrime a' b' ∧ c' * a' = 
a ∧ c' * b' = b
-/
theorem exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
    ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

end UniqueFactorizationMonoid

