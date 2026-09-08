/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Unique factorization and normalization

## Main definitions
* `UniqueFactorizationMonoid.normalizedFactors`: choose a multiset of prime factors that are unique
  by normalizing them.
* `UniqueFactorizationMonoid.normalizationMonoid`: choose a way of normalizing the elements of a UFM
-/

@[expose] public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [NormalizationMonoid α]
variable [UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
/-
**UniqueFactorizationMonoid.normalizedFactors** 是 Mathlib 中的一个定义，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：normalizedFactors (a : α) : Multiset α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably determines the multiset of prime factors.
-/
noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp]
/-
**UniqueFactorizationMonoid.factors_eq_normalizedFactors** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：factors_eq_normalizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFac
torizationMonoid M] [Subsingleton Mˣ] (x : M) : factors x = normalizedFactors x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s

--- 原说明 ---
An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set
 of factors,
if `M` has a trivial group of units.
-/
theorem factors_eq_normalizedFactors {M : Type*} [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Subsingleton Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm with p
  exact normalize_eq p
/-
**UniqueFactorizationMonoid.prod_normalizedFactors** 是 Mathlib 中的一个定理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：prod_normalizedFactors {a : α} (ane0 : a != 0) : Associated (normalizedFac
tors a).prod a
参数：ane0 : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.eq_1`：∀ {α : Type u_1} [inst
 : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : UniqueFactor
izationMonoid α]   (a : α), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `UniqueFactorizationMonoid.factors.eq_1`：∀ {α : Type u_1} [inst : CommMon
oidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a : α),   UniqueFactoriza
tionMonoid.factors a = if h …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Associates.mk_normalize`：Associates.mk_normalize (x : α) : Associates.mk
 (normalize x) = Associates.mk x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem prod_normalizedFactors {a : α} (ane0 : a ≠ 0) :
    Associated (normalizedFactors a).prod a := by
  rw [normalizedFactors, factors, dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk,
    Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply, Associates.mk_normalize]
/-
**UniqueFactorizationMonoid.prod_normalizedFactors_eq** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：prod_normalizedFactors_eq {α} [CommMonoidWithZero α] [StrongNormalizationM
onoid α] [UniqueFactorizationMonoid α] {a : α} (ane0 : a != 0) : (normalizedFact
ors a).prod = normalize a
参数：ane0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.eq_1`：∀ {α : Type u_1} [inst
 : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : UniqueFactor
izationMonoid α]   (a : α), UniqueFact…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_normalizeHom`：coe_normalizeHom : normalizeHom (α
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `normalize_idem`：normalize_idem (x : α) : normalize (normalize x) = norma
lize x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `normalize_eq_normalize_iff`：normalize_eq_normalize_iff {x y : α} : norma
lize x = normalize y ↔ x ∣ y ∧ y ∣ x
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `dvd_dvd_iff_associated`：dvd_dvd_iff_associated [MonoidWithZero M] [IsLef
tCancelMulZero M] {a b : M} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
theorem prod_normalizedFactors_eq {α} [CommMonoidWithZero α] [StrongNormalizationMonoid α]
    [UniqueFactorizationMonoid α] {a : α} (ane0 : a ≠ 0) :
    (normalizedFactors a).prod = normalize a := by
  trans normalize (normalizedFactors a).prod
  · rw [normalizedFactors, ← coe_normalizeHom, ← map_multiset_prod, coe_normalizeHom,
      normalize_idem]
  · exact normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr (prod_normalizedFactors ane0))
/-
**UniqueFactorizationMonoid.prime_of_normalized_factor** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：prime_of_normalized_factor {a : α} : forall x : α, x in normalizedFactors 
a -> Prime x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.eq_1`：∀ {α : Type u_1} [inst
 : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : UniqueFactor
izationMonoid α]   (a : α), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `UniqueFactorizationMonoid.factors.eq_1`：∀ {α : Type u_1} [inst : CommMon
oidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a : α),   UniqueFactoriza
tionMonoid.factors a = if h …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Associated.prime_iff`：Associated.prime_iff [CommMonoidWithZero M] {p q :
 M} (h : p ~ᵤ q) : Prime p ↔ Prime q
· 使用定理 `normalize_associated`：normalize_associated (x : α) : Associated (normali
ze x) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Prime x := by
  rw [normalizedFactors, factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy
/-
**UniqueFactorizationMonoid.irreducible_of_normalized_factor** 是 Mathlib 中的一个定理，
位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：irreducible_of_normalized_factor {a : α} : forall x : α, x in normalizedFa
ctors a -> Irreducible x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
-/
theorem irreducible_of_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).irreducible
/-
**UniqueFactorizationMonoid.normalize_normalized_factor** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：normalize_normalized_factor {a : α} : forall x : α, x in normalizedFactors
 a -> normalize x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.eq_1`：∀ {α : Type u_1} [inst
 : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : UniqueFactor
izationMonoid α]   (a : α), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `UniqueFactorizationMonoid.factors.eq_1`：∀ {α : Type u_1} [inst : CommMon
oidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a : α),   UniqueFactoriza
tionMonoid.factors a = if h …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `normalize_idem`：normalize_idem (x : α) : normalize (normalize x) = norma
lize x
-/
theorem normalize_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → normalize x = x := by
  rw [normalizedFactors, factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem
/-
**UniqueFactorizationMonoid.normalizedFactors_irreducible** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_irreducible {a : α} (ha : Irreducible a) : normalizedFac
tors a = {normalize a}
参数：ha : Irreducible a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prime_factors_irreducible`：prime_factors_irreducible [CommMonoidWithZero
 α] {a : α} {f : Multiset α} (ha : Irreducible a) (pfa : (forall b in f, Prime b
) ∧ f.prod ~ᵤ a…
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Mu
ltiset α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `normalize_eq_normalize_iff`：normalize_eq_normalize_iff {x y : α} : norma
lize x = normalize y ↔ x ∣ y ∧ y ∣ x
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `dvd_dvd_iff_associated`：dvd_dvd_iff_associated [MonoidWithZero M] [IsLef
tCancelMulZero M] {a b : M} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b
-/
theorem normalizedFactors_irreducible {a : α} (ha : Irreducible a) :
    normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, prod_normalizedFactors ha.ne_zero⟩
  have p_mem : p ∈ normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert! hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]
/-
**UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_eq_of_dvd (a : α) : forallᵉ (p in normalizedFactors a) (
q in normalizedFactors a), p ∣ q -> p = q
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `normalize_eq_normalize`：normalize_eq_normalize {a b : α} (hab : a ∣ b) (
hba : b ∣ a) : normalize a = normalize b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
-/
theorem normalizedFactors_eq_of_dvd (a : α) :
    ∀ᵉ (p ∈ normalizedFactors a) (q ∈ normalizedFactors a), p ∣ q → p = q := by
  intro p hp q hq hdvd
  convert!
    normalize_eq_normalize hdvd
      ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
        (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm
/-
**UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd** 是 Mathlib 中的一个
定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：exists_mem_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreduc
ible p) : p ∣ a -> exists q in normalizedFactors a, p ~ᵤ q
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
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `Multiset.exists_mem_of_rel_of_mem`：exists_mem_of_rel_of_mem {r : α -> β 
-> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) : forall {a : α}, a i
n s -> exists b in t, r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_mem_normalizedFactors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ normalizedFactors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun _ hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := prod_normalizedFactors ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (prod_normalizedFactors hb0).symm.mul_left _)
  Multiset.exists_mem_of_rel_of_mem this (by simp)
/-
**UniqueFactorizationMonoid.exists_mem_normalizedFactors** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：exists_mem_normalizedFactors {x : α} (hx : x != 0) (h : ¬IsUnit x) : exist
s p, p in normalizedFactors x
参数：hx : x != 0；h : ¬IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
-/
theorem exists_mem_normalizedFactors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) :
    ∃ p, p ∈ normalizedFactors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：normalizedFactors_zero : normalizedFactors (0 : α) = 0
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
theorem normalizedFactors_zero : normalizedFactors (0 : α) = 0 := by
  simp [normalizedFactors, factors]

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：normalizedFactors_one : normalizedFactors (1 : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniqueFactorizationMonoid.exists_prime_factors`：exists_prime_factors (a 
: α) : a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_zero_right`：rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a
 = 0
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem normalizedFactors_one : normalizedFactors (1 : α) = 0 := by
  rcases subsingleton_or_nontrivial α with h | h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.notMem_zero x hx
    · apply prod_normalizedFactors one_ne_zero

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：normalizedFactors_mul {x y : α} (hx : x != 0) (hy : y != 0) : normalizedFa
ctors (x * y) = normalizedFactors x + normalizedFactors y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Associates.out_mk`：out_mk (a : α) : (Associates.mk a).out = normalize a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_mk_eq_map_mk_of_rel`：map_mk_eq_map_mk_of_rel {r : α -> α ->
 Prop} {s t : Multiset α} (hst : s.Rel r t) : s.map (Quot.mk r) = t.map (Quot.mk
 r)
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Associated.mul_mul`：Associated.mul_mul [CommMonoid M] {a₁ a₂ b₁ b₂ : M} 
(h₁ : a₁ ~ᵤ b₁) (h₂ : a₂ ~ᵤ b₂) : a₁ * a₂ ~ᵤ b₁ * b₂
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
-/
theorem normalizedFactors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    normalizedFactors (x * y) = normalizedFactors x + normalizedFactors y := by
  have h : (normalize : α → α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_apply, Associates.out_mk]
  rw [← Multiset.map_id' (normalizedFactors (x * y)), ← Multiset.map_id' (normalizedFactors x), ←
    Multiset.map_id' (normalizedFactors y), ← Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_congr rfl normalize_normalized_factor, ← Multiset.map_add, h, ←
    Multiset.map_map Associates.out, eq_comm, ← Multiset.map_map Associates.out]
  refine congr rfl ?_
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
  · exact irreducible_of_normalized_factor
  · rw [Multiset.prod_add]
    exact
      ((prod_normalizedFactors hx).mul_mul (prod_normalizedFactors hy)).trans
        (prod_normalizedFactors (mul_ne_zero hx hy)).symm

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactors_pow** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：normalizedFactors_pow {x : α} (n : Nat) : normalizedFactors (x ^ n) = n • 
normalizedFactors x
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.congr_simp`：∀ {α : Type u_1}
 [inst : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : Unique
FactorizationMonoid α]   (a a_1 : α), a = a_…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
-/
theorem normalizedFactors_pow {x : α} (n : ℕ) :
    normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    rw [pow_succ', succ_nsmul', normalizedFactors_mul h0 (pow_ne_zero _ h0), ih]
/-
**UniqueFactorizationMonoid._root_.Irreducible.normalizedFactors_pow** 是 Mathlib
 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible hp,
    Multiset.nsmul_singleton]
/-
**UniqueFactorizationMonoid.normalizedFactors_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_prod_eq (s : Multiset α) (hs : forall a in s, Irreducibl
e a) : normalizedFactors s.prod = s.map normalize
参数：s : Multiset α；hs : forall a in s, Irreducible a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Multiset.empty_or_exists_mem`：empty_or_exists_mem (s : Multiset α) : s =
 0 ∨ exists a, a in s
· 使用定理 `Multiset.cons_zero`：cons_zero (a : α) : a ::ₘ 0 = {a}
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用引理 `Multiset.prod_ne_zero`：prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
-/
theorem normalizedFactors_prod_eq (s : Multiset α) (hs : ∀ a ∈ s, Irreducible a) :
    normalizedFactors s.prod = s.map normalize := by
  induction s using Multiset.induction with
  | empty => rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  | cons a s ih =>
    have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    have := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons, Multiset.map_cons,
      normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl),
      normalizedFactors_irreducible ia, ih ib, Multiset.singleton_add]
/-
**UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors** 是 M
athlib 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy
 : y != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Multiset.instCanonicallyOrderedAdd`：∀ {α : Type u_1}, CanonicallyOrdered
Add (Multiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associated.dvd_iff_dvd_left`：Associated.dvd_iff_dvd_left [Monoid M] {a b
 c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
-/
theorem dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ normalizedFactors x ≤ normalizedFactors y := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (prod_normalizedFactors hx).dvd_iff_dvd_left, ←
      (prod_normalizedFactors hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
/-
**UniqueFactorizationMonoid._root_.Associated.normalizedFactors_eq** 是 Mathlib 中
的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.normalizedFactors_eq {a b : α} (h : Associated a b) :
    normalizedFactors a = normalizedFactors b := by
  unfold normalizedFactors
  have h' : normalize (α := α) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h', ← Multiset.map_map, ← Multiset.map_map,
    Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]
/-
**UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactor
s** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：associated_iff_normalizedFactors_eq_normalizedFactors {x y : α} (hx : x !=
 0) (hy : y != 0) : x ~ᵤ y ↔ normalizedFactors x = normalizedFactors y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.normalizedFactors_eq`：∀ {α : Type u_1} [inst : CommMonoidWith
Zero α] [inst_1 : NormalizationMonoid α] [inst_2 : UniqueFactorizationMonoid α] 
  {a b : α},   Associ…
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
-/
theorem associated_iff_normalizedFactors_eq_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ~ᵤ y ↔ normalizedFactors x = normalizedFactors y :=
  ⟨Associated.normalizedFactors_eq, fun h =>
    (prod_normalizedFactors hx).symm.trans (_root_.trans (by rw [h]) (prod_normalizedFactors hy))⟩
/-
**UniqueFactorizationMonoid.normalizedFactors_of_irreducible_pow** 是 Mathlib 中的一
个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : Nat
) : normalizedFactors (p ^ k) = Multiset.replicate k (normalize p)
参数：hp : Irreducible p；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
-/
theorem normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible hp, Multiset.nsmul_singleton]
/-
**UniqueFactorizationMonoid.zero_notMem_normalizedFactors** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
形式化陈述：zero_notMem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
-/
theorem zero_notMem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl
/-
**UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors** 是 Mathlib 中的一个定理，
位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：ne_zero_of_mem_normalizedFactors {x a : α} (hx : x in normalizedFactors a)
 : x != 0
参数：hx : x in normalizedFactors a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`：zero_notMem_nor
malizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
-/
theorem ne_zero_of_mem_normalizedFactors {x a : α} (hx : x ∈ normalizedFactors a) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx <| zero_notMem_normalizedFactors a
/-
**UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：dvd_of_mem_normalizedFactors {a p : α} (H : p in normalizedFactors a) : p 
∣ a
参数：H : p in normalizedFactors a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
theorem dvd_of_mem_normalizedFactors {a p : α} (H : p ∈ normalizedFactors a) : p ∣ a := by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (prod_normalizedFactors hcases))
/-
**UniqueFactorizationMonoid.mem_normalizedFactors_iff** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：mem_normalizedFactors_iff [Subsingleton αˣ] {p x : α} (hx : x != 0) : p in
 normalizedFactors x ↔ Prime p ∧ p ∣ x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
-/
theorem mem_normalizedFactors_iff [Subsingleton αˣ] {p x : α} (hx : x ≠ 0) :
    p ∈ normalizedFactors x ↔ Prime p ∧ p ∣ x := by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem
/-
**UniqueFactorizationMonoid.mem_normalizedFactors_iff'** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：mem_normalizedFactors_iff' {p x : α} (h : x != 0) : p in normalizedFactors
 x ↔ Irreducible p ∧ normalize p = p ∧ p ∣ x
参数：h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_factors_of_dvd`：exists_mem_factors_
of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a -> exists q in fact
ors a, p ~ᵤ q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `normalize_eq_normalize_iff_associated`：normalize_eq_normalize_iff_associ
ated {a b : α} : normalize a = normalize b ↔ Associated a b where mp h
· 使用定理 `Associated.comm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y ↔ Associated y x
-/
theorem mem_normalizedFactors_iff' {p x : α} (h : x ≠ 0) :
    p ∈ normalizedFactors x ↔ Irreducible p ∧ normalize p = p ∧ p ∣ x := by
  refine ⟨fun h ↦ ⟨irreducible_of_normalized_factor p h, normalize_normalized_factor p h,
    dvd_of_mem_normalizedFactors h⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by
    rwa [← h₂, normalize_eq_normalize_iff_associated, Associated.comm]⟩

/-- Relatively prime elements have disjoint prime factors (as multisets). -/
/-
**UniqueFactorizationMonoid.disjoint_normalizedFactors** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：disjoint_normalizedFactors {a b : α} (hc : IsRelPrime a b) : Disjoint (nor
malizedFactors a) (normalizedFactors b)
参数：hc : IsRelPrime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x

--- 原说明 ---
Relatively prime elements have disjoint prime factors (as multisets).
-/
theorem disjoint_normalizedFactors {a b : α} (hc : IsRelPrime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  exact (prime_of_normalized_factor x hxa).not_isUnit (hc x_dvd_a x_dvd_b)
/-
**UniqueFactorizationMonoid.exists_associated_prime_pow_of_unique_normalized_fac
tor** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：exists_associated_prime_pow_of_unique_normalized_factor {p r : α} (h : for
all {m}, m in normalizedFactors r -> m = p) (hr : r != 0) : exists i : Nat, Asso
ciated (p ^ i) r
参数：h : forall {m}, m in normalizedFactors r -> m = p；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {s : Multiset α},
 (∀ b ∈ s, b = a) → s = Multiset.replicate s.card a
-/
theorem exists_associated_prime_pow_of_unique_normalized_factor {p r : α}
    (h : ∀ {m}, m ∈ normalizedFactors r → m = p) (hr : r ≠ 0) : ∃ i : ℕ, Associated (p ^ i) r := by
  use (normalizedFactors r).card
  have := UniqueFactorizationMonoid.prod_normalizedFactors hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this
/-
**UniqueFactorizationMonoid.normalizedFactors_prod_of_prime** 是 Mathlib 中的一个定理，位
于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_prod_of_prime [Subsingleton αˣ] {m : Multiset α} (h : fo
rall p in m, Prime p) : normalizedFactors m.prod = m
参数：h : forall p in m, Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `prime_factors_unique`：prime_factors_unique [CommMonoidWithZero α] [IsCan
celMulZero α] : forall {f g : Multiset α}, (forall x in f, Prime x) -> (forall x
 in g, Pri…
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Multiset.prod_ne_zero_of_prime`：prod_ne_zero_of_prime [CommMonoidWithZer
o M₀] [NoZeroDivisors M₀] [Nontrivial M₀] (s : Multiset M₀) (h : forall x in s, 
Prime x) : s.prod !=…
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
-/
theorem normalizedFactors_prod_of_prime [Subsingleton αˣ] {m : Multiset α}
    (h : ∀ p ∈ m, Prime p) : normalizedFactors m.prod = m := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx ↦ ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (prod_normalizedFactors (m.prod_ne_zero_of_prime h))
/-
**UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated** 是 Mathlib 中
的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a in normalizedFa
ctors c) (hb : b in normalizedFactors c) (h : Associated a b) : a = b
参数：ha : a in normalizedFactors c；hb : b in normalizedFactors c；h : Associated a 
b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `normalize_eq_normalize_iff`：normalize_eq_normalize_iff {x y : α} : norma
lize x = normalize y ↔ x ∣ y ∧ y ∣ x
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Associated.dvd_dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associ
ated a b → a ∣ b ∧ b ∣ a
-/
theorem mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a ∈ normalizedFactors c)
    (hb : b ∈ normalizedFactors c) (h : Associated a b) : a = b := by
  rw [← normalize_normalized_factor a ha, ← normalize_normalized_factor b hb,
    normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactors_pos** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：normalizedFactors_pos (x : α) (hx : x != 0) : 0 < normalizedFactors x ↔ ¬I
sUnit x
参数：x : α；hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors`：exists_mem_norma
lizedFactors {x : α} (hx : x != 0) (h : ¬IsUnit x) : exists p, p in normalizedFa
ctors x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem normalizedFactors_pos (x : α) (hx : x ≠ 0) : 0 < normalizedFactors x ↔ ¬IsUnit x := by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact
      (prime_of_normalized_factor _ hp).not_isUnit
        (isUnit_of_dvd_unit (dvd_of_mem_normalizedFactors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

/--
The multiset of normalized factors of `x` is nil if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `normalizedFactors_of_isUnit`.
-/
/-
**UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_eq_zero_iff {x : α} (hx : x != 0) : normalizedFactors x 
= 0 ↔ IsUnit x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pos`：normalizedFactors_pos (
x : α) (hx : x != 0) : 0 < normalizedFactors x ↔ ¬IsUnit x
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Multiset.instCanonicallyOrderedAdd`：∀ {α : Type u_1}, CanonicallyOrdered
Add (Multiset α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The multiset of normalized factors of `x` is nil if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `normalizedFactors_of_i
sUnit`.
-/
theorem normalizedFactors_eq_zero_iff {x : α} (hx : x ≠ 0) :
    normalizedFactors x = 0 ↔ IsUnit x := by
  rw [← not_iff_not, ← normalizedFactors_pos _ hx, pos_iff_ne_zero]

/--
If `x` is a unit, then the multiset of normalized factors of `x` is nil.
The converse is true with a nonzero assumption, see `normalizedFactors_eq_zero_iff`.
-/
/-
**UniqueFactorizationMonoid.normalizedFactors_of_isUnit** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_of_isUnit {x : α} (hx : IsUnit x) : normalizedFactors x 
= 0
参数：hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff`：normalizedFacto
rs_eq_zero_iff {x : α} (hx : x != 0) : normalizedFactors x = 0 ↔ IsUnit x

--- 原说明 ---
If `x` is a unit, then the multiset of normalized factors of `x` is nil.
The converse is true with a nonzero assumption, see `normalizedFactors_eq_zero_i
ff`.
-/
theorem normalizedFactors_of_isUnit {x : α} (hx : IsUnit x) :
    normalizedFactors x = 0 := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · simp
  rwa [normalizedFactors_eq_zero_iff hx₀]
/-
**UniqueFactorizationMonoid.dvdNotUnit_iff_normalizedFactors_lt_normalizedFactor
s** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors {x y : α} (hx : x !=
 0) (hy : y != 0) : DvdNotUnit x y ↔ normalizedFactors x < normalizedFactors y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Multiset.instIsOrderedCancelAddMonoid`：∀ {α : Type u_1}, IsOrderedCancel
AddMonoid (Multiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvdNotUnit_of_dvd_of_not_dvd`：dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd
 : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    DvdNotUnit x y ↔ normalizedFactors x < normalizedFactors y := by
  constructor
  · rintro ⟨_, c, hc, rfl⟩
    simp only [hx, right_ne_zero_of_mul hy, normalizedFactors_mul, Ne, not_false_iff,
      lt_add_iff_pos_right, normalizedFactors_pos, hc]
  · intro h
    exact
      dvdNotUnit_of_dvd_of_not_dvd
        ((dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mpr h.le)
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_ge)
/-
**UniqueFactorizationMonoid.normalizedFactors_multiset_prod** 是 Mathlib 中的一个定理，位
于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) : normalized
Factors (s.prod) = (s.map normalizedFactors).sum
参数：s : Multiset α；hs : 0 ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用引理 `Multiset.prod_ne_zero`：prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) :
    normalizedFactors (s.prod) = (s.map normalizedFactors).sum := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro _
      convert! hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, normalizedFactors_mul, IH]
    · exact fun h ↦ hs (Multiset.mem_cons_of_mem h)
    · exact fun h ↦ hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h ↦ hs (Multiset.mem_cons_of_mem h)

variable {β : Type*} [CommMonoidWithZero β] [NormalizationMonoid β]
  [UniqueFactorizationMonoid β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β] {f : F}

/--
If the monoid equiv `f : α ≃* β` commutes with `normalize` then, for `a : α`, it yields a
bijection between the `normalizedFactors` of `a` and of `f a`.
-/
/-
**UniqueFactorizationMonoid.normalizedFactorsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：normalizedFactorsEquiv (he : forall x, normalize (f x) = f (normalize x)) 
(a : α) : {x // x in normalizedFactors a} ≃ {y // y in normalizedFactors (f a)}
参数：he : forall x, normalize (f x) = f (normalize x)；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the monoid equiv `f : α ≃* β` commutes with `normalize` then, for `a : α`, it
 yields a
bijection between the `normalizedFactors` of `a` and of `f a`.
-/
def normalizedFactorsEquiv (he : ∀ x, normalize (f x) = f (normalize x)) (a : α) :
    {x // x ∈ normalizedFactors a} ≃ {y // y ∈ normalizedFactors (f a)} :=
  Equiv.subtypeEquiv f fun x ↦ by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simp [mem_normalizedFactors_iff' ha,
        mem_normalizedFactors_iff' (EmbeddingLike.map_ne_zero_iff.mpr ha), map_dvd_iff_dvd_symm,
        MulEquiv.irreducible_iff, he]

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactorsEquiv_apply** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactorsEquiv_apply (he : forall x, normalize (f x) = f (normaliz
e x)) {a p : α} (hp : p in normalizedFactors a) : normalizedFactorsEquiv he a ⟨p
, hp⟩ = f p
参数：he : forall x, normalize (f x) = f (normalize x)；hp : p in normalizedFactors 
a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizedFactorsEquiv_apply (he : ∀ x, normalize (f x) = f (normalize x))
    {a p : α} (hp : p ∈ normalizedFactors a) :
    normalizedFactorsEquiv he a ⟨p, hp⟩ = f p := rfl

@[simp]
/-
**UniqueFactorizationMonoid.normalizedFactorsEquiv_symm_apply** 是 Mathlib 中的一个定理
，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactorsEquiv_symm_apply (he : forall x, normalize (f x) = f (nor
malize x)) {a : α} {q : β} (hq : q in normalizedFactors (f a)) : (normalizedFact
orsEquiv he a).symm ⟨q, hq⟩ = (MulEquivClass.toMulEquiv f).symm q
参数：he : forall x, normalize (f x) = f (normalize x)；hq : q in normalizedFactors 
(f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem normalizedFactorsEquiv_symm_apply (he : ∀ x, normalize (f x) = f (normalize x))
    {a : α} {q : β} (hq : q ∈ normalizedFactors (f a)) :
    (normalizedFactorsEquiv he a).symm ⟨q, hq⟩ = (MulEquivClass.toMulEquiv f).symm q := rfl

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Multiset Associates

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

open scoped Classical in
/-- Noncomputably defines a `StrongNormalizationMonoid` structure on a `UniqueFactorizationMonoid`.
-/
@[instance_reducible]
/-
**UniqueFactorizationMonoid.strongNormalizationMonoid** 是 Mathlib 中的一个定义，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：{α : Type u_1} → [inst : CommMonoidWithZero α] → [UniqueFactorizationMonoi
d α] → StrongNormalizationMonoid α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α

--- 原说明 ---
Noncomputably defines a `StrongNormalizationMonoid` structure on a `UniqueFactor
izationMonoid`.
-/
protected noncomputable def strongNormalizationMonoid : StrongNormalizationMonoid α :=
  strongNormalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α → α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α → Associates α) := by
        ext x
        rw [Function.comp_apply, mkMonoidHom_apply,
          Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx, ← mkMonoidHom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ←
        associated_iff_eq]
      apply prod_normalizedFactors hx)

@[deprecated (since := "2026-07-08")]
protected alias normalizationMonoid := UniqueFactorizationMonoid.strongNormalizationMonoid
/-
**UniqueFactorizationMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `UniqueFactorizationMonoi
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Nonempty (StrongNormalizationMonoid α) :=
  ⟨UniqueFactorizationMonoid.strongNormalizationMonoid⟩

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Multiset

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/-
**UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset** 是 Mathlib
 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_prod_eq_self_of_subset [Subsingleton αˣ] {a : α} {m : Mu
ltiset α} (hm : m subseteq normalizedFactors a) : normalizedFactors m.prod = m
参数：hm : m subseteq normalizedFactors a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_prod_of_prime`：normalizedFac
tors_prod_of_prime [Subsingleton αˣ] {m : Multiset α} (h : forall p in m, Prime 
p) : normalizedFactors m.prod = m
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
-/
lemma normalizedFactors_prod_eq_self_of_subset [Subsingleton αˣ] {a : α} {m : Multiset α}
    (hm : m ⊆ normalizedFactors a) :
    normalizedFactors m.prod = m :=
  normalizedFactors_prod_of_prime fun _ h ↦ prime_of_normalized_factor _ (mem_of_subset hm h)
/-
**UniqueFactorizationMonoid.prod_ne_zero_of_subset_normalizedFactors** 是 Mathlib
 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：prod_ne_zero_of_subset_normalizedFactors [NormalizationMonoid α] [Nontrivi
al α] {a : α} {m : Multiset α} (hm : m subseteq normalizedFactors a) : m.prod !=
 0
参数：hm : m subseteq normalizedFactors a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_ne_zero_of_prime`：prod_ne_zero_of_prime [CommMonoidWithZer
o M₀] [NoZeroDivisors M₀] [Nontrivial M₀] (s : Multiset M₀) (h : forall x in s, 
Prime x) : s.prod !=…
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
-/
lemma prod_ne_zero_of_subset_normalizedFactors [NormalizationMonoid α] [Nontrivial α] {a : α}
    {m : Multiset α} (hm : m ⊆ normalizedFactors a) :
    m.prod ≠ 0 :=
  prod_ne_zero_of_prime _ fun _ h ↦ prime_of_normalized_factor _ (mem_of_subset hm h)

variable [DecidableEq α]
/-
**UniqueFactorizationMonoid.normalizedFactors_prod_inter_eq_inter** 是 Mathlib 中的
一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：normalizedFactors_prod_inter_eq_inter [Subsingleton αˣ] (a b : α) : normal
izedFactors (normalizedFactors a inter normalizedFactors b).prod = normalizedFac
tors a inter normalizedFactors b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset`：norm
alizedFactors_prod_eq_self_of_subset [Subsingleton αˣ] {a : α} {m : Multiset α} 
(hm : m subseteq normalizedFactors a) : normalizedFactor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Multiset.mem_inter`：mem_inter : a in s inter t ↔ a in s ∧ a in t
-/
lemma normalizedFactors_prod_inter_eq_inter [Subsingleton αˣ] (a b : α) :
    normalizedFactors (normalizedFactors a ∩ normalizedFactors b).prod =
      normalizedFactors a ∩ normalizedFactors b :=
  normalizedFactors_prod_eq_self_of_subset fun _ h ↦ (mem_inter.mp h).left
/-
**UniqueFactorizationMonoid.prod_inter_normalizedFactors_ne_zero** 是 Mathlib 中的一
个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：prod_inter_normalizedFactors_ne_zero [NormalizationMonoid α] [Nontrivial α
] (a b : α) : (normalizedFactors a inter normalizedFactors b).prod != 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniqueFactorizationMonoid.prod_ne_zero_of_subset_normalizedFactors`：prod
_ne_zero_of_subset_normalizedFactors [NormalizationMonoid α] [Nontrivial α] {a :
 α} {m : Multiset α} (hm : m subseteq normalizedFactors …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Multiset.mem_inter`：mem_inter : a in s inter t ↔ a in s ∧ a in t
-/
lemma prod_inter_normalizedFactors_ne_zero [NormalizationMonoid α] [Nontrivial α] (a b : α) :
    (normalizedFactors a ∩ normalizedFactors b).prod ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors fun _ h ↦ (mem_inter.mp h).left

end UniqueFactorizationMonoid

