/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Submonoid.Primal
public import Mathlib.Order.WellFounded

/-!
# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`
-/

@[expose] public section

assert_not_exists Field Finsupp Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of ∣, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
-/
/-
**WfDvdMonoid** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Well-foundedness of the strict version of ∣, which is equivalent to the descendi
ng chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
-/
abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit
/-
**wellFounded_dvdNotUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid
 α] : WellFounded (DvdNotUnit (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem wellFounded_dvdNotUnit {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid α] :
    WellFounded (DvdNotUnit (α := α)) :=
  h.wf

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

variable [WfDvdMonoid α]

/-
**WfDvdMonoid.exists_irreducible_factor** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdMonoid`。
形式化陈述：exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a != 0) : exists
 i, Irreducible i ∧ i ∣ a
参数：ha : ¬IsUnit a；ha0 : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
-/
theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) :
    ∃ i, Irreducible i ∧ i ∣ a :=
  let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[elab_as_elim]
/-
**WfDvdMonoid.induction_on_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdMonoid`。
形式化陈述：induction_on_irreducible {motive : α -> Prop} (a : α) (zero : motive 0) (u
nit : forall u : α, IsUnit u -> motive u) (mul : forall a i : α, a != 0 -> Irred
ucible i -> motive a -> motive (i * a)) : motive a
参数：a : α；zero : motive 0；unit : forall u : α, IsUnit u -> motive u；mul : forall 
a i : α, a != 0 -> Irreducible i -> motive a -> motive (i * a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
-/
theorem induction_on_irreducible {motive : α → Prop} (a : α)
    (zero : motive 0) (unit : ∀ u : α, IsUnit u → motive u)
    (mul : ∀ a i : α, a ≠ 0 → Irreducible i → motive a → motive (i * a)) : motive a :=
  haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr zero
      else
        if hau : IsUnit a then unit a hau
        else
          let ⟨i, i_irred, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩
          hb.symm ▸ mul b i hb0 i_irred <| ih b ⟨hb0, i, i_irred.1, mul_comm i b ▸ hb⟩)
    a
/-
**WfDvdMonoid.exists_factors** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdMonoid`。
形式化陈述：exists_factors (a : α) : a != 0 -> exists f : Multiset α, (forall b in f, 
Irreducible b) ∧ Associated f.prod a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.induction_on_irreducible`：induction_on_irreducible {motive :
 α -> Prop} (a : α) (zero : motive 0) (unit : forall u : α, IsUnit u -> motive u
) (mul : forall a i : α, a…
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a :=
  induction_on_irreducible a (fun h => (h rfl).elim)
    (fun _ hu _ => ⟨0, fun _ h => False.elim (Multiset.notMem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.prod_cons i]
      exact hs.2.mul_left i⟩
/-
**WfDvdMonoid.not_isUnit_iff_exists_factors_eq** 是 Mathlib 中的一个定理，位于命名空间 `WfDvdM
onoid`。
形式化陈述：not_isUnit_iff_exists_factors_eq (a : α) (hn0 : a != 0) : ¬IsUnit a ↔ exis
ts f : Multiset α, (forall b in f, Irreducible b) ∧ f.prod = a ∧ f != ∅
参数：a : α；hn0 : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.exists_factors`：exists_factors (a : α) : a != 0 -> exists f 
: Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Associated.irreducible`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}, As
sociated p q → Irreducible p → Irreducible q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.mem_of_mem_erase`：mem_of_mem_erase {a b : α} {s : Multiset α} :
 a in s.erase b -> a in s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Multiset.prod_erase`：prod_erase [DecidableEq M] (h : a in s) : a * (s.er
ase a).prod = s.prod
· 使用定理 `Multiset.cons_ne_zero`：cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m !
= 0
· 使用定理 `not_isUnit_of_not_isUnit_dvd`：not_isUnit_of_not_isUnit_dvd {a b : α} (ha
 : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
-/
theorem not_isUnit_iff_exists_factors_eq (a : α) (hn0 : a ≠ 0) :
    ¬IsUnit a ↔ ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod = a ∧ f ≠ ∅ :=
  ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
    obtain ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero fun h : f = 0 => hnu <| by simp [h]
    classical
      refine ⟨(f.erase b).cons (b * u), fun a ha => ?_, ?_, Multiset.cons_ne_zero⟩
      · obtain rfl | ha := Multiset.mem_cons.1 ha
        exacts [Associated.irreducible ⟨u, rfl⟩ (hi b h), hi a (Multiset.mem_of_mem_erase ha)]
      · rw [Multiset.prod_cons, mul_comm b, mul_assoc, Multiset.prod_erase h, mul_comm],
    fun ⟨_, hi, he, hne⟩ =>
    let ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero hne
    not_isUnit_of_not_isUnit_dvd (hi b h).not_isUnit <| he ▸ Multiset.dvd_prod h⟩

@[deprecated (since := "2026-08-02")]
alias not_unit_iff_exists_factors_eq := not_isUnit_iff_exists_factors_eq
/-
**WfDvdMonoid.isRelPrime_of_no_irreducible_factors** 是 Mathlib 中的一个定理，位于命名空间 `Wf
DvdMonoid`。
形式化陈述：isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)
) (H : forall z : α, Irreducible z -> z ∣ x -> ¬z ∣ y) : IsRelPrime x y
参数：nonzero : ¬(x = 0 ∧ y = 0)；H : forall z : α, Irreducible z -> z ∣ x -> ¬z ∣ y
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isRelPrime_of_no_nonunits_factors`：isRelPrime_of_no_nonunits_factors [Mo
noidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z, ¬ IsUnit z
 -> z != 0 -> z ∣ x -> …
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
theorem isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : α, Irreducible z → z ∣ x → ¬z ∣ y) : IsRelPrime x y :=
  isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy ↦
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

end WfDvdMonoid

section Prio

-- set_option default_priority 100

-- see Note [default priority]
/--
Unique factorization monoids are defined as cancellative `CommMonoidWithZero`s with well-founded
strict divisibility relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_existsUnique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`
-/
@[wikidata Q1052579 "This Mathlib declaration captures 'unique factorization'.
Use in conjunction with `IsDomain` to capture unique factorization domain."]
/-
**UniqueFactorizationMonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [CommMonoidWithZero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class UniqueFactorizationMonoid (α : Type*) [CommMonoidWithZero α] : Prop
    extends IsCancelMulZero α, IsWellFounded α DvdNotUnit where
  protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a

attribute [instance 100] UniqueFactorizationMonoid.toIsCancelMulZero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ufm_of_decomposition_of_wfDvdMonoid
    [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] [DecompositionMonoid α] :
    UniqueFactorizationMonoid α where
  irreducible_iff_prime := irreducible_iff_prime

end Prio

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/-
**UniqueFactorizationMonoid.exists_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 `Uniq
ueFactorizationMonoid`。
形式化陈述：exists_prime_factors (a : α) : a != 0 -> exists f : Multiset α, (forall b 
in f, Prime b) ∧ f.prod ~ᵤ a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `WfDvdMonoid.exists_factors`：exists_factors (a : α) : a != 0 -> exists f 
: Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
-/
theorem exists_prime_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a
/-
**UniqueFactorizationMonoid.exists_prime_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：exists_prime_iff : (exists (p : α), Prime p) ↔ exists (x : α), x != 0 ∧ ¬ 
IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
-/
lemma exists_prime_iff :
    (∃ (p : α), Prime p) ↔ ∃ (x : α), x ≠ 0 ∧ ¬ IsUnit x := by
  refine ⟨fun ⟨p, hp⟩ ↦ ⟨p, hp.ne_zero, hp.not_isUnit⟩, fun ⟨x, hx₀, hxu⟩ ↦ ?_⟩
  obtain ⟨f, hf, -⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx₀
  exact ⟨f, UniqueFactorizationMonoid.irreducible_iff_prime.mp hf⟩

@[elab_as_elim]
/-
**UniqueFactorizationMonoid.induction_on_prime** 是 Mathlib 中的一个定理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：induction_on_prime {P : α -> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, 
IsUnit x -> P x) (h₃ : forall a p : α, a != 0 -> Prime p -> P a -> P (p * a)) : 
P a
参数：a : α；h₁ : P 0；h₂ : forall x : α, IsUnit x -> P x；h₃ : forall a p : α, a != 0
 -> Prime p -> P a -> P (p * a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.induction_on_irreducible`：induction_on_irreducible {motive :
 α -> Prop} (a : α) (zero : motive 0) (unit : forall u : α, IsUnit u -> motive u
) (mul : forall a i : α, a…
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem induction_on_prime {P : α → Prop} (a : α) (h₁ : P 0) (h₂ : ∀ x : α, IsUnit x → P x)
    (h₃ : ∀ a p : α, a ≠ 0 → Prime p → P a → P (p * a)) : P a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃
/-
**UniqueFactorizationMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `UniqueFactorizationMonoi
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecompositionMonoid α where
  primal a := by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · · |>.isPrimal)).mul u.isUnit.isPrimal

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α]

variable (α) in
/-
**UniqueFactorizationMonoid.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：of_subsingleton [Subsingleton α] : UniqueFactorizationMonoid α where mul_l
eft_cancel_of_ne_zero _ a b _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_subsingleton [Subsingleton α] : UniqueFactorizationMonoid α where
  mul_left_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  mul_right_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  wf := ⟨fun a ↦ Acc.intro a fun b ⟨hb, _⟩ ↦ (hb (Subsingleton.elim b 0)).elim⟩
  irreducible_iff_prime {a} := by simp [Subsingleton.elim a 0]

variable [UniqueFactorizationMonoid α]

open scoped Classical in
/-- Noncomputably determines the multiset of prime factors. -/
/-
**UniqueFactorizationMonoid.factors** 是 Mathlib 中的一个定义，位于命名空间 `UniqueFactorizati
onMonoid`。
形式化陈述：factors (a : α) : Multiset α
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a

--- 原说明 ---
Noncomputably determines the multiset of prime factors.
-/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)
/-
**UniqueFactorizationMonoid.factors_prod** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：factors_prod {a : α} (ane0 : a != 0) : Associated (factors a).prod a
参数：ane0 : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.factors.eq_1`：∀ {α : Type u_1} [inst : CommMon
oidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a : α),   UniqueFactoriza
tionMonoid.factors a = if h …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem factors_prod {a : α} (ane0 : a ≠ 0) : Associated (factors a).prod a := by
  rw [factors, dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2

@[simp]
/-
**UniqueFactorizationMonoid.factors_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：factors_zero : factors (0 : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem factors_zero : factors (0 : α) = 0 := by simp [factors]
/-
**UniqueFactorizationMonoid.ne_zero_of_mem_factors** 是 Mathlib 中的一个定理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：ne_zero_of_mem_factors {p a : α} (h : p in factors a) : a != 0
参数：h : p in factors a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.factors_zero`：factors_zero : factors (0 : α) =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_mem_factors {p a : α} (h : p ∈ factors a) : a ≠ 0 := by
  rintro rfl
  simp at h
/-
**UniqueFactorizationMonoid.dvd_of_mem_factors** 是 Mathlib 中的一个定理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：dvd_of_mem_factors {p a : α} (h : p in factors a) : p ∣ a
参数：h : p in factors a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `UniqueFactorizationMonoid.ne_zero_of_mem_factors`：ne_zero_of_mem_factors
 {p a : α} (h : p in factors a) : a != 0
-/
theorem dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))
/-
**UniqueFactorizationMonoid.prime_of_factor** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：prime_of_factor {a : α} (x : α) (hx : x in factors a) : Prime x
参数：x : α；hx : x in factors a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.ne_zero_of_mem_factors`：ne_zero_of_mem_factors
 {p a : α} (h : p in factors a) : a != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `UniqueFactorizationMonoid.factors.eq_1`：∀ {α : Type u_1} [inst : CommMon
oidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a : α),   UniqueFactoriza
tionMonoid.factors a = if h …
-/
theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors, dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx
/-
**UniqueFactorizationMonoid.irreducible_of_factor** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：irreducible_of_factor {a : α} : forall x : α, x in factors a -> Irreducibl
e x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
-/
theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x := fun x h =>
  (prime_of_factor x h).irreducible

open Multiset in
/-
**UniqueFactorizationMonoid.card_factors_of_irreducible** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：card_factors_of_irreducible {a : α} (ha : Irreducible a) : (factors a).car
d = 1
参数：ha : Irreducible a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associated.irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}
, Associated p q → (Irreducible p ↔ Irreducible q)
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem card_factors_of_irreducible {a : α} (ha : Irreducible a) : (factors a).card = 1 := by
  have hf : factors a ≠ 0 := by
    intro hf
    simpa [hf, Associated.comm, ha.not_isUnit] using factors_prod ha.ne_zero
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero hf
  obtain ⟨f, hf⟩ := exists_cons_of_mem hb
  rw [hf, card_cons, add_eq_right, card_eq_zero, eq_zero_iff_forall_notMem]
  intro c hc
  obtain ⟨f, rfl⟩ := exists_cons_of_mem hc
  replace hb := (irreducible_of_factor b hb).not_isUnit
  replace hc := (irreducible_of_factor c (hf ▸ mem_cons_of_mem hc)).not_isUnit
  simp [← (factors_prod ha.ne_zero).irreducible_iff, hf, irreducible_mul_iff, hb, hc] at ha

end UniqueFactorizationMonoid

