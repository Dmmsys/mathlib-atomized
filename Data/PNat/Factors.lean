/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.PNat.Prime
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `PrimeMultiset`: Type of multisets of prime numbers.
* `FactorMultiset n`: Multiset of prime factors of `n`.
-/

@[expose] public section

/-- The type of multisets of prime numbers.  Unique factorization
gives an equivalence between this set and ℕ+, as we will formalize
below. -/
/-
**PrimeMultiset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeMultiset
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of multisets of prime numbers.  Unique factorization
gives an equivalence between this set and ℕ+, as we will formalize
below.
-/
def PrimeMultiset :=
  Multiset Nat.Primes
deriving Inhabited, AddCommMonoid, SemilatticeSup, DistribLattice,
  Sub, IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
/-
**PrimeMultiset.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeMultiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset; infer_instance

/-- The multiset consisting of a single prime -/
/-
**PrimeMultiset.ofPrime** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：ofPrime (p : Nat.Primes) : PrimeMultiset
参数：p : Nat.Primes。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset consisting of a single prime
-/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)

@[simp]
/-
**PrimeMultiset.card_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl

/-- We can forget the primality property and regard a multiset
of primes as just a multiset of positive integers, or a multiset
of natural numbers.  In the opposite direction, if we have a
multiset of positive integers or natural numbers, together with
a proof that all the elements are prime, then we can regard it
as a multiset of primes.  The next block of results records
obvious properties of these coercions.
-/
/-
**PrimeMultiset.toNatMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：toNatMultiset : PrimeMultiset -> Multiset Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can forget the primality property and regard a multiset
of primes as just a multiset of positive integers, or a multiset
of natural numbers.  In the opposite direction, if we have a
multiset of positive integers or natural numbers, together with
a proof that all the elements are prime, then we can regard it
as a multiset of primes.  The next block of results records
obvious properties of these coercions.
-/
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map (↑)
/-
**PrimeMultiset.coeNat** 是 Mathlib 中的一个实例，位于命名空间 `PrimeMultiset`。
形式化陈述：coeNat : Coe PrimeMultiset (Multiset Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩

/-- `PrimeMultiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `AddMonoidHom`. -/
/-
**PrimeMultiset.coeNatMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：coeNatMonoidHom : PrimeMultiset ->+ Multiset Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PrimeMultiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `AddMonoidHom`.
-/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
/-
**PrimeMultiset.coe_coeNatMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset -> Multiset Nat) = 
(↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = (↑) :=
  rfl
/-
**PrimeMultiset.coeNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coeNat_injective : Function.Injective ((↑) : PrimeMultiset -> Multiset Nat
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Nat.Primes.coe_nat_injective`：coe_nat_injective : Function.Injective ((↑
) : Nat.Primes -> Nat)
-/
theorem coeNat_injective : Function.Injective ((↑) : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective
/-
**PrimeMultiset.coeNat_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset Nat) = {(p : Nat)}
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {(p : ℕ)} :=
  rfl
/-
**PrimeMultiset.coeNat_prime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coeNat_prime (v : PrimeMultiset) (p : Nat) (h : p in (v : Multiset Nat)) :
 p.Prime
参数：v : PrimeMultiset；p : Nat；h : p in (v : Multiset Nat)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem coeNat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

/-- Converts a `PrimeMultiset` to a `Multiset ℕ+`. -/
/-
**PrimeMultiset.toPNatMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：toPNatMultiset : PrimeMultiset -> Multiset Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `PrimeMultiset` to a `Multiset ℕ+`.
-/
def toPNatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map (↑)
/-
**PrimeMultiset.coePNat** 是 Mathlib 中的一个实例，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNat : Coe PrimeMultiset (Multiset Nat+)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coePNat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPNatMultiset⟩

/-- `coePNat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `AddMonoidHom`. -/
/-
**PrimeMultiset.coePNatMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNatMonoidHom : PrimeMultiset ->+ Multiset Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coePNat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `AddMonoidHom`.
-/
def coePNatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
/-
**PrimeMultiset.coe_coePNatMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset -> Multiset Nat+)
 = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset → Multiset ℕ+) = (↑) :=
  rfl
/-
**PrimeMultiset.coePNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNat_injective : Function.Injective ((↑) : PrimeMultiset -> Multiset Na
t+)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Nat.Primes.coe_pnat_injective`：coe_pnat_injective : Function.Injective (
(↑) : Nat.Primes -> Nat+)
-/
theorem coePNat_injective : Function.Injective ((↑) : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective
/-
**PrimeMultiset.coePNat_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset Nat+) = {(p : Nat
+)}
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl
/-
**PrimeMultiset.coePNat_prime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNat_prime (v : PrimeMultiset) (p : Nat+) (h : p in (v : Multiset Nat+)
) : p.Prime
参数：v : PrimeMultiset；p : Nat+；h : p in (v : Multiset Nat+)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem coePNat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'
/-
**PrimeMultiset.coeMultisetPNatNat** 是 Mathlib 中的一个实例，位于命名空间 `PrimeMultiset`。
形式化陈述：coeMultisetPNatNat : Coe (Multiset Nat+) (Multiset Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeMultisetPNatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map (↑)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**PrimeMultiset.coePNat_nat** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coePNat_nat (v : PrimeMultiset) : ((v : Multiset Nat+) : Multiset Nat) = (
v : Multiset Nat)
参数：v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem coePNat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) := by
  change (v.map ((↑) : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  rfl

/-- The product of a `PrimeMultiset`, as a `ℕ+`. -/
/-
**PrimeMultiset.prod** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：prod (v : PrimeMultiset) : Nat+
参数：v : PrimeMultiset。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a `PrimeMultiset`, as a `ℕ+`.
-/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset PNat).prod

set_option backward.isDefEq.respectTransparency false in
/-
**PrimeMultiset.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：coe_prod (v : PrimeMultiset) : (v.prod : Nat) = (v : Multiset Nat).prod
参数：v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
-/
theorem coe_prod (v : PrimeMultiset) : (v.prod : ℕ) = (v : Multiset ℕ).prod := by
  have h : (v.prod : ℕ) = ((v.map (↑) : Multiset ℕ+).map (↑)).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  simpa [Multiset.map_map] using! h
/-
**PrimeMultiset.prod_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_ofPrime (p : Nat.Primes) : (ofPrime p).prod = (p : Nat+)
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).prod = (p : ℕ+) :=
  Multiset.prod_singleton _

/-- If a `Multiset ℕ` consists only of primes, it can be recast as a `PrimeMultiset`. -/
/-
**PrimeMultiset.ofNatMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：ofNatMultiset (v : Multiset Nat) (h : forall p : Nat, p in v -> p.Prime) :
 PrimeMultiset
参数：v : Multiset Nat；h : forall p : Nat, p in v -> p.Prime。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `Multiset ℕ` consists only of primes, it can be recast as a `PrimeMultiset`
.
-/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PrimeMultiset.mem_ofNatMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：mem_ofNatMultiset {p : Nat+} {s : Multiset Nat} (hs) : p in (ofNatMultiset
 s hs : Multiset Nat+) ↔ (p : Nat) in s
参数：hs。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ofNatMultiset {p : ℕ+} {s : Multiset ℕ} (hs) :
    p ∈ (ofNatMultiset s hs : Multiset ℕ+) ↔ (p : ℕ) ∈ s := by
  simp only [ofNatMultiset, toPNatMultiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat,
    ← PNat.coe_inj]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PrimeMultiset.to_ofNatMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：to_ofNatMultiset (v : Multiset Nat) (h) : (ofNatMultiset v h : Multiset Na
t) = v
参数：v : Multiset Nat；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem to_ofNatMultiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v := by
  dsimp [ofNatMultiset, toNatMultiset]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']

@[simp]
/-
**PrimeMultiset.prod_ofNatMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_ofNatMultiset (v : Multiset Nat) (h) : ((ofNatMultiset v h).prod : Na
t) = (v.prod : Nat)
参数：v : Multiset Nat；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.coe_prod`：coe_prod (v : PrimeMultiset) : (v.prod : Nat) = 
(v : Multiset Nat).prod
· 使用定理 `PrimeMultiset.to_ofNatMultiset`：to_ofNatMultiset (v : Multiset Nat) (h) 
: (ofNatMultiset v h : Multiset Nat) = v
-/
theorem prod_ofNatMultiset (v : Multiset ℕ) (h) :
    ((ofNatMultiset v h).prod : ℕ) = (v.prod : ℕ) := by rw [coe_prod, to_ofNatMultiset]

/-- If a `Multiset ℕ+` consists only of primes, it can be recast as a `PrimeMultiset`. -/
/-
**PrimeMultiset.ofPNatMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：ofPNatMultiset (v : Multiset Nat+) (h : forall p : Nat+, p in v -> p.Prime
) : PrimeMultiset
参数：v : Multiset Nat+；h : forall p : Nat+, p in v -> p.Prime。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `Multiset ℕ+` consists only of primes, it can be recast as a `PrimeMultiset
`.
-/
def ofPNatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PrimeMultiset.to_ofPNatMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：to_ofPNatMultiset (v : Multiset Nat+) (h) : (ofPNatMultiset v h : Multiset
 Nat+) = v
参数：v : Multiset Nat+；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem to_ofPNatMultiset (v : Multiset ℕ+) (h) : (ofPNatMultiset v h : Multiset ℕ+) = v := by
  dsimp [ofPNatMultiset, toPNatMultiset]
  have : (fun (p : ℕ+) (h : p.Prime) => ((↑) : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.ext
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]

@[simp]
/-
**PrimeMultiset.prod_ofPNatMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_ofPNatMultiset (v : Multiset Nat+) (h) : ((ofPNatMultiset v h).prod :
 Nat+) = v.prod
参数：v : Multiset Nat+；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.to_ofPNatMultiset`：to_ofPNatMultiset (v : Multiset Nat+) (
h) : (ofPNatMultiset v h : Multiset Nat+) = v
-/
theorem prod_ofPNatMultiset (v : Multiset ℕ+) (h) : ((ofPNatMultiset v h).prod : ℕ+) = v.prod := by
  dsimp [prod]
  rw [to_ofPNatMultiset]

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
/-
**PrimeMultiset.ofNatList** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：ofNatList (l : List Nat) (h : forall p : Nat, p in l -> p.Prime) : PrimeMu
ltiset
参数：l : List Nat；h : forall p : Nat, p in l -> p.Prime。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets.
-/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PrimeMultiset.mem_ofNatList** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：mem_ofNatList {p : Nat+} {l : List Nat} (hl) : p in (ofNatList l hl : Mult
iset Nat+) ↔ (p : Nat) in l
参数：hl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ofNatList {p : ℕ+} {l : List ℕ} (hl) :
    p ∈ (ofNatList l hl : Multiset ℕ+) ↔ (p : ℕ) ∈ l := by
  simp [ofNatList]

@[simp]
/-
**PrimeMultiset.prod_ofNatList** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_ofNatList (l : List Nat) (h) : ((ofNatList l h).prod : Nat) = l.prod
参数：l : List Nat；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeMultiset.prod_ofNatMultiset`：prod_ofNatMultiset (v : Multiset Nat) 
(h) : ((ofNatMultiset v h).prod : Nat) = (v.prod : Nat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
-/
theorem prod_ofNatList (l : List ℕ) (h) : ((ofNatList l h).prod : ℕ) = l.prod := by
  have := prod_ofNatMultiset (l : Multiset ℕ) h
  rw [Multiset.prod_coe] at this
  exact this

/-- If a `List ℕ+` consists only of primes, it can be recast as a `PrimeMultiset` with
the coercion from lists to multisets. -/
/-
**PrimeMultiset.ofPNatList** 是 Mathlib 中的一个定义，位于命名空间 `PrimeMultiset`。
形式化陈述：ofPNatList (l : List Nat+) (h : forall p : Nat+, p in l -> p.Prime) : Prim
eMultiset
参数：l : List Nat+；h : forall p : Nat+, p in l -> p.Prime。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `List ℕ+` consists only of primes, it can be recast as a `PrimeMultiset` wi
th
the coercion from lists to multisets.
-/
def ofPNatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset ℕ+) h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PrimeMultiset.toPNatMultiset_ofPNatList** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultis
et`。
形式化陈述：toPNatMultiset_ofPNatList {l : List Nat+} (hl) : (ofPNatList l hl : Multis
et Nat+) = l
参数：hl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.to_ofPNatMultiset`：to_ofPNatMultiset (v : Multiset Nat+) (
h) : (ofPNatMultiset v h : Multiset Nat+) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPNatMultiset_ofPNatList {l : List ℕ+} (hl) : (ofPNatList l hl : Multiset ℕ+) = l := by
  simp [ofPNatList]

@[simp]
/-
**PrimeMultiset.prod_ofPNatList** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_ofPNatList (l : List Nat+) (h) : (ofPNatList l h).prod = l.prod
参数：l : List Nat+；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeMultiset.prod_ofPNatMultiset`：prod_ofPNatMultiset (v : Multiset Nat
+) (h) : ((ofPNatMultiset v h).prod : Nat+) = v.prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
-/
theorem prod_ofPNatList (l : List ℕ+) (h) : (ofPNatList l h).prod = l.prod := by
  have := prod_ofPNatMultiset (l : Multiset ℕ+) h
  rw [Multiset.prod_coe] at this
  exact this

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
@[simp]
/-
**PrimeMultiset.prod_zero** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_zero : (0 : PrimeMultiset).prod = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1

--- 原说明 ---
The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+.
-/
theorem prod_zero : (0 : PrimeMultiset).prod = 1 := by
  exact Multiset.prod_zero

@[simp]
/-
**PrimeMultiset.prod_add** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_add (u v : PrimeMultiset) : (u + v).prod = u.prod * v.prod
参数：u v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
-/
theorem prod_add (u v : PrimeMultiset) : (u + v).prod = u.prod * v.prod := by
  change (coePNatMonoidHom (u + v)).prod = _
  rw [coePNatMonoidHom.map_add]
  exact Multiset.prod_add _ _

@[simp]
/-
**PrimeMultiset.prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_smul (d : Nat) (u : PrimeMultiset) : (d • u).prod = u.prod ^ d
参数：d : Nat；u : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `PrimeMultiset.prod_zero`：prod_zero : (0 : PrimeMultiset).prod = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `PrimeMultiset.prod_add`：prod_add (u v : PrimeMultiset) : (u + v).prod = 
u.prod * v.prod
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).prod = u.prod ^ d := by
  induction d with
  | zero => simp only [zero_nsmul, pow_zero, prod_zero]
  | succ n ih => rw [succ_nsmul, prod_add, ih, pow_succ]

end PrimeMultiset

namespace PNat

/-- The prime factors of n, regarded as a multiset -/
/-
**PNat.factorMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：factorMultiset (n : Nat+) : PrimeMultiset
参数：n : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime factors of n, regarded as a multiset
-/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

/-- The product of the factors is the original number -/
@[simp]
/-
**PNat.prod_factorMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：prod_factorMultiset (n : Nat+) : (factorMultiset n).prod = n
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.prod_ofNatList`：prod_ofNatList (l : List Nat) (h) : ((ofNa
tList l h).prod : Nat) = l.prod
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `PNat.ne_zero`：ne_zero (n : Nat+) : (n : Nat) != 0

--- 原说明 ---
The product of the factors is the original number
-/
theorem prod_factorMultiset (n : ℕ+) : (factorMultiset n).prod = n :=
  eq <| by
    dsimp [factorMultiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_primeFactorsList n.ne_zero
/-
**PNat.coeNat_factorMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coeNat_factorMultiset (n : Nat+) : (factorMultiset n : Multiset Nat) = (Na
t.primeFactorsList n : Multiset Nat)
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeMultiset.to_ofNatMultiset`：to_ofNatMultiset (v : Multiset Nat) (h) 
: (ofNatMultiset v h : Multiset Nat) = v
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
-/
theorem coeNat_factorMultiset (n : ℕ+) :
    (factorMultiset n : Multiset ℕ) = (Nat.primeFactorsList n : Multiset ℕ) :=
  PrimeMultiset.to_ofNatMultiset (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

@[simp]
/-
**PNat.mem_factorMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mem_factorMultiset {p n : Nat+} : p in (n.factorMultiset : Multiset Nat+) 
↔ p.Prime ∧ p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_factorMultiset {p n : ℕ+} : p ∈ (n.factorMultiset : Multiset ℕ+) ↔ p.Prime ∧ p ∣ n := by
  simp [factorMultiset, dvd_iff, PNat.Prime]

end PNat

namespace PrimeMultiset

set_option backward.isDefEq.respectTransparency false in
/-- If we start with a multiset of primes, take the product and
then factor it, we get back the original multiset. -/
@[simp]
/-
**PrimeMultiset.factorMultiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：factorMultiset_prod (v : PrimeMultiset) : v.prod.factorMultiset = v
参数：v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeMultiset.coeNat_injective`：coeNat_injective : Function.Injective ((
↑) : PrimeMultiset -> Multiset Nat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.coeNat_factorMultiset`：coeNat_factorMultiset (n : Nat+) : (factorMu
ltiset n : Multiset Nat) = (Nat.primeFactorsList n : Multiset Nat)
· 使用定理 `PrimeMultiset.coe_prod`：coe_prod (v : PrimeMultiset) : (v.prod : Nat) = 
(v : Multiset Nat).prod
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_subtype`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {l : Li
st { x // p x }} {f : { x // p x } → β} {g : α → β},   (∀ (x : α) (h : p x), f ⟨
x, h⟩ …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `Nat.primeFactorsList_unique`：primeFactorsList_unique {n : Nat} {l : List
 Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p) : l ~ primeFactorsList n

--- 原说明 ---
If we start with a multiset of primes, take the product and
then factor it, we get back the original multiset.
-/
theorem factorMultiset_prod (v : PrimeMultiset) : v.prod.factorMultiset = v := by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coeNat_factorMultiset, PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  dsimp [PrimeMultiset.toNatMultiset]
  let l' := l.map ((↑) : Nat.Primes → ℕ)
  have (p : ℕ) (hp : p ∈ l') : p.Prime := by
    simp only [List.map_subtype, List.map_id_fun', id_eq, List.mem_unattach, l'] at hp
    obtain ⟨hp', -⟩ := hp
    exact hp'
  exact Multiset.coe_eq_coe.mpr (@Nat.primeFactorsList_unique _ l' rfl this).symm

end PrimeMultiset

namespace PNat

/-- Positive integers biject with multisets of primes. -/
/-
**PNat.factorMultisetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：factorMultisetEquiv : Nat+ ≃ PrimeMultiset where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v

--- 原说明 ---
Positive integers biject with multisets of primes.
-/
def factorMultisetEquiv : ℕ+ ≃ PrimeMultiset where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod

set_option backward.isDefEq.respectTransparency false in
/-- Factoring gives a homomorphism from the multiplicative
monoid ℕ+ to the additive monoid of multisets. -/
@[simp]
/-
**PNat.factorMultiset_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_one : factorMultiset 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.pmap.congr_simp`：∀ {α : Type u_1} {β : Type v} {p : α → Prop} (
f f_1 : (a : α) → p a → β),   f = f_1 → ∀ (s s_1 : Multiset α) (e_s : s = s_1) (
a : ∀ a ∈ s, p…
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Factoring gives a homomorphism from the multiplicative
monoid ℕ+ to the additive monoid of multisets.
-/
theorem factorMultiset_one : factorMultiset 1 = 0 := by
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

@[simp]
/-
**PNat.factorMultiset_mul** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_mul (n m : Nat+) : factorMultiset (n * m) = factorMultiset 
n + factorMultiset m
参数：n m : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.prod_add`：prod_add (u v : PrimeMultiset) : (u + v).prod = 
u.prod * v.prod
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
-/
theorem factorMultiset_mul (n m : ℕ+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m := by
  let u := factorMultiset n
  let v := factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

@[simp]
/-
**PNat.factorMultiset_pow** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_pow (n : Nat+) (m : Nat) : factorMultiset (n ^ m) = m • fac
torMultiset n
参数：n : Nat+；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.prod_smul`：prod_smul (d : Nat) (u : PrimeMultiset) : (d • 
u).prod = u.prod ^ d
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
-/
theorem factorMultiset_pow (n : ℕ+) (m : ℕ) :
    factorMultiset (n ^ m) = m • factorMultiset n := by
  let u := factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  rw [this, ← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

/-- Factoring a prime gives the corresponding one-element multiset. -/
/-
**PNat.factorMultiset_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_ofPrime (p : Nat.Primes) : (p : Nat+).factorMultiset = Prim
eMultiset.ofPrime p
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `PrimeMultiset.prod_ofPrime`：prod_ofPrime (p : Nat.Primes) : (ofPrime p).
prod = (p : Nat+)

--- 原说明 ---
Factoring a prime gives the corresponding one-element multiset.
-/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p := by
  apply factorMultisetEquiv.symm.injective
  change (p : ℕ+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  rw [(p : ℕ+).prod_factorMultiset, PrimeMultiset.prod_ofPrime]

/-- We now have four different results that all encode the
idea that inequality of multisets corresponds to divisibility
of positive integers. -/
@[simp]
/-
**PNat.factorMultiset_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_le_iff {m n : Nat+} : factorMultiset m <= factorMultiset n 
↔ m ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `PrimeMultiset.prod_add`：prod_add (u v : PrimeMultiset) : (u + v).prod = 
u.prod * v.prod
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `instCanonicallyOrderedAddPrimeMultiset`：CanonicallyOrderedAdd PrimeMulti
set
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `instIsOrderedCancelAddMonoidPrimeMultiset`：IsOrderedCancelAddMonoid Prim
eMultiset
· 使用定理 `instOrderedSubPrimeMultiset`：OrderedSub PrimeMultiset
· 使用定理 `PNat.mul_div_exact`：mul_div_exact {m k : Nat+} (h : k ∣ m) : k * divExac
t m k = m
· 使用定理 `PNat.factorMultiset_mul`：factorMultiset_mul (n m : Nat+) : factorMultise
t (n * m) = factorMultiset n + factorMultiset m
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b

--- 原说明 ---
We now have four different results that all encode the
idea that inequality of multisets corresponds to divisibility
of positive integers.
-/
theorem factorMultiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n := by
  constructor
  · intro h
    rw [← prod_factorMultiset m, ← prod_factorMultiset m]
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factorMultiset_prod, add_tsub_cancel_of_le h,
      prod_factorMultiset]
  · intro h
    rw [← mul_div_exact h, factorMultiset_mul]
    exact le_self_add

@[gcongr]
alias ⟨_, factorMultiset_mono⟩ := factorMultiset_le_iff
/-
**PNat.factorMultiset_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_le_iff' {m : Nat+} {v : PrimeMultiset} : factorMultiset m <
= v ↔ m ∣ v.prod
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.factorMultiset_le_iff`：factorMultiset_le_iff {m n : Nat+} : factorM
ultiset m <= factorMultiset n ↔ m ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
-/
theorem factorMultiset_le_iff' {m : ℕ+} {v : PrimeMultiset} :
    factorMultiset m ≤ v ↔ m ∣ v.prod := by
  let h := @factorMultiset_le_iff m v.prod
  rw [v.factorMultiset_prod] at h
  exact h

end PNat

namespace PrimeMultiset

@[simp]
/-
**PrimeMultiset.prod_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u <= v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.factorMultiset_le_iff'`：factorMultiset_le_iff' {m : Nat+} {v : Prim
eMultiset} : factorMultiset m <= v ↔ m ∣ v.prod
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
-/
theorem prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u ≤ v := by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factorMultiset_prod] at h
  exact h.symm

@[gcongr] alias ⟨_, prod_dvd_prod⟩ := prod_dvd_iff
/-
**PrimeMultiset.prod_dvd_iff'** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_dvd_iff' {u : PrimeMultiset} {n : Nat+} : u.prod ∣ n ↔ u <= n.factorM
ultiset
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeMultiset.prod_dvd_iff`：prod_dvd_iff {u v : PrimeMultiset} : u.prod 
∣ v.prod ↔ u <= v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
-/
theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factorMultiset := by
  let h := @prod_dvd_iff u n.factorMultiset
  rw [n.prod_factorMultiset] at h
  exact h

end PrimeMultiset

namespace PNat

/-- The gcd and lcm operations on positive integers correspond
to the inf and sup operations on multisets. -/
/-
**PNat.factorMultiset_gcd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_gcd (m n : Nat+) : factorMultiset (gcd m n) = factorMultise
t m ⊓ factorMultiset n
参数：m n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `PNat.factorMultiset_le_iff`：factorMultiset_le_iff {m n : Nat+} : factorM
ultiset m <= factorMultiset n ↔ m ∣ n
· 使用定理 `PNat.gcd_dvd_left`：gcd_dvd_left (n m : Nat+) : gcd n m ∣ n
· 使用定理 `PNat.gcd_dvd_right`：gcd_dvd_right (n m : Nat+) : gcd n m ∣ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeMultiset.prod_dvd_iff`：prod_dvd_iff {u v : PrimeMultiset} : u.prod 
∣ v.prod ↔ u <= v
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `PNat.dvd_gcd`：dvd_gcd {m n k : Nat+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd
 m n
· 使用定理 `PrimeMultiset.prod_dvd_iff'`：prod_dvd_iff' {u : PrimeMultiset} {n : Nat+
} : u.prod ∣ n ↔ u <= n.factorMultiset
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
The gcd and lcm operations on positive integers correspond
to the inf and sup operations on multisets.
-/
theorem factorMultiset_gcd (m n : ℕ+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n := by
  apply le_antisymm
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact gcd_dvd_left m n
    · exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    · exact inf_le_left
    · exact inf_le_right
/-
**PNat.factorMultiset_lcm** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：factorMultiset_lcm (m n : Nat+) : factorMultiset (lcm m n) = factorMultise
t m ⊔ factorMultiset n
参数：m n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeMultiset.prod_dvd_iff`：prod_dvd_iff {u v : PrimeMultiset} : u.prod 
∣ v.prod ↔ u <= v
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
· 使用定理 `PNat.lcm_dvd`：lcm_dvd {m n k : Nat+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n
 ∣ k
· 使用定理 `PNat.factorMultiset_le_iff'`：factorMultiset_le_iff' {m : Nat+} {v : Prim
eMultiset} : factorMultiset m <= v ↔ m ∣ v.prod
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `PNat.factorMultiset_le_iff`：factorMultiset_le_iff {m n : Nat+} : factorM
ultiset m <= factorMultiset n ↔ m ∣ n
· 使用定理 `PNat.dvd_lcm_left`：dvd_lcm_left (n m : Nat+) : n ∣ lcm n m
· 使用定理 `PNat.dvd_lcm_right`：dvd_lcm_right (n m : Nat+) : m ∣ lcm n m
-/
theorem factorMultiset_lcm (m n : ℕ+) :
    factorMultiset (lcm m n) = factorMultiset m ⊔ factorMultiset n := by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply lcm_dvd <;> rw [← factorMultiset_le_iff']
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact dvd_lcm_left m n
    · exact dvd_lcm_right m n

set_option backward.isDefEq.respectTransparency false in
/-- The number of occurrences of p in the factor multiset of m
is the same as the p-adic valuation of m. -/
/-
**PNat.count_factorMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：count_factorMultiset (m : Nat+) (p : Nat.Primes) (k : Nat) : (p : Nat+) ^ 
k ∣ m ↔ k <= m.factorMultiset.count p
参数：m : Nat+；p : Nat.Primes；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.le_count_iff_replicate_le`：le_count_iff_replicate_le {a : α} {s
 : Multiset α} {n : Nat} : n <= count a s ↔ replicate n a <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.factorMultiset_le_iff`：factorMultiset_le_iff {m n : Nat+} : factorM
ultiset m <= factorMultiset n ↔ m ∣ n
· 使用定理 `PNat.factorMultiset_pow`：factorMultiset_pow (n : Nat+) (m : Nat) : facto
rMultiset (n ^ m) = m • factorMultiset n
· 使用定理 `PNat.factorMultiset_ofPrime`：factorMultiset_ofPrime (p : Nat.Primes) : (
p : Nat+).factorMultiset = PrimeMultiset.ofPrime p
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用引理 `Multiset.card_nsmul`：card_nsmul (s : Multiset α) (n : Nat) : card (n • s
) = n * card s
· 使用定理 `PrimeMultiset.card_ofPrime`：card_ofPrime (p : Nat.Primes) : Multiset.car
d (ofPrime p) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
· 使用定理 `PrimeMultiset.ofPrime.eq_1`：∀ (p : Nat.Primes), PrimeMultiset.ofPrime p 
= {p}

--- 原说明 ---
The number of occurrences of p in the factor multiset of m
is the same as the p-adic valuation of m.
-/
theorem count_factorMultiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) :
    (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factorMultiset.count p := by
  rw [Multiset.le_count_iff_replicate_le, ← factorMultiset_le_iff, factorMultiset_pow,
    factorMultiset_ofPrime]
  congr! 2
  apply Multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_replicate h

end PNat

namespace PrimeMultiset

/-
**PrimeMultiset.prod_inf** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_inf (u v : PrimeMultiset) : (u ⊓ v).prod = PNat.gcd u.prod v.prod
参数：u v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.factorMultiset_gcd`：factorMultiset_gcd (m n : Nat+) : factorMultise
t (gcd m n) = factorMultiset m ⊓ factorMultiset n
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
-/
theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).prod = PNat.gcd u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).prod = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m, PNat.prod_factorMultiset]
/-
**PrimeMultiset.prod_sup** 是 Mathlib 中的一个定理，位于命名空间 `PrimeMultiset`。
形式化陈述：prod_sup (u v : PrimeMultiset) : (u ⊔ v).prod = PNat.lcm u.prod v.prod
参数：u v : PrimeMultiset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeMultiset.factorMultiset_prod`：factorMultiset_prod (v : PrimeMultise
t) : v.prod.factorMultiset = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.factorMultiset_lcm`：factorMultiset_lcm (m n : Nat+) : factorMultise
t (lcm m n) = factorMultiset m ⊔ factorMultiset n
· 使用定理 `PNat.prod_factorMultiset`：prod_factorMultiset (n : Nat+) : (factorMultis
et n).prod = n
-/
theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).prod = PNat.lcm u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).prod = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m, PNat.prod_factorMultiset]

end PrimeMultiset

