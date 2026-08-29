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

/--
Definition of `PrimeMultiset` / `PrimeMultiset` 的定义

English:
definition PrimeMultiset
  body: Multiset Nat.Primes
deriving Inhabited, AddCommMonoid, SemilatticeSup, DistribLattice,
  Sub, IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

中文:
定义 PrimeMultiset
  定义体: Multiset Nat.Primes
deriving Inhabited, AddCommMonoid, SemilatticeSup, DistribLattice,
  Sub, IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

Depends on / 依赖: Multiset, Nat.Primes, Primes
-/
def PrimeMultiset :=
  Multiset Nat.Primes
deriving Inhabited, AddCommMonoid, SemilatticeSup, DistribLattice,
  Sub, IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset; infer_instance

/--
Definition of `ofPrime` / `ofPrime` 的定义

English:
definition ofPrime
  signature: (p : Nat.Primes)
  body: ({p} : Multiset Nat.Primes)

@[simp]

中文:
定义 ofPrime
  签名: (p : 自然数.Primes)
  定义体: ({p} : Multiset Nat.Primes)

@[simp]

Depends on / 依赖: Multiset, Nat.Primes, Primes
-/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)

@[simp]
/--
theorem `card_ofPrime` / 定理 `card_ofPrime`

English:
theorem card_ofPrime
  given: (p : Nat.Primes)
  statement: Multiset.card (ofPrime p) = 1
  proof: rfl

中文:
定理 card_ofPrime
  条件: (p : 自然数.Primes)
  结论: Multiset.card (ofPrime p) = 1
  证明: rfl
-/
theorem card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl

/--
Definition of `toNatMultiset` / `toNatMultiset` 的定义

English:
definition toNatMultiset
  signature: : PrimeMultiset -> Multiset Nat
  body: fun v => v.map (↑)

中文:
定义 toNatMultiset
  签名: : PrimeMultiset -> Multiset 自然数
  定义体: fun v => v.map (↑)

Depends on / 依赖: v.map
-/
def toNatMultiset : PrimeMultiset -> Multiset Nat := fun v => v.map (↑)

/--
Instance `coeNat` / 实例 `coeNat`

English:
instance coeNat
  signature: : Coe PrimeMultiset (Multiset Nat)
  body: ⟨toNatMultiset⟩

中文:
实例 coeNat
  签名: : Coe PrimeMultiset (Multiset 自然数)
  定义体: ⟨toNatMultiset⟩

Depends on / 依赖: toNatMultiset
-/
instance coeNat : Coe PrimeMultiset (Multiset Nat) :=
  ⟨toNatMultiset⟩

/--
Definition of `coeNatMonoidHom` / `coeNatMonoidHom` 的定义

English:
definition coeNatMonoidHom
  signature: : PrimeMultiset ->+ Multiset Nat
  body: Multiset.mapAddMonoidHom (↑)

@[simp]

中文:
定义 coeNatMonoidHom
  签名: : PrimeMultiset ->+ Multiset 自然数
  定义体: Multiset.mapAddMonoidHom (↑)

@[simp]

Depends on / 依赖: Multiset, Multiset.mapAddMonoidHom, mapAddMonoidHom
-/
def coeNatMonoidHom : PrimeMultiset ->+ Multiset Nat :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
/--
theorem `coe_coeNatMonoidHom` / 定理 `coe_coeNatMonoidHom`

English:
theorem coe_coeNatMonoidHom
  statement: (coeNatMonoidHom : PrimeMultiset -> Multiset Nat) = (↑)
  proof: rfl

中文:
定理 coe_coeNatMonoidHom
  结论: (coe自然数MonoidHom : PrimeMultiset -> Multiset 自然数) = (↑)
  证明: rfl
-/
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset -> Multiset Nat) = (↑) :=
  rfl

/--
theorem `coeNat_injective` / 定理 `coeNat_injective`

English:
theorem coeNat_injective
  statement: Function.Injective ((↑) : PrimeMultiset -> Multiset Nat)
  proof: Multiset.map_injective Nat.Primes.coe_nat_injective

中文:
定理 coeNat_injective
  结论: Function.Injective ((↑) : PrimeMultiset -> Multiset 自然数)
  证明: Multiset.map_injective Nat.Primes.coe_nat_injective

Depends on / 依赖: Multiset, Multiset.map_injective, Nat.Primes.coe_nat_injective, Primes, coe_nat_injective, map_injective
-/
theorem coeNat_injective : Function.Injective ((↑) : PrimeMultiset -> Multiset Nat) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective

/--
theorem `coeNat_ofPrime` / 定理 `coeNat_ofPrime`

English:
theorem coeNat_ofPrime
  given: (p : Nat.Primes)
  statement: (ofPrime p : Multiset Nat) = {(p : Nat)}
  proof: rfl

中文:
定理 coeNat_ofPrime
  条件: (p : 自然数.Primes)
  结论: (ofPrime p : Multiset 自然数) = {(p : 自然数)}
  证明: rfl
-/
theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset Nat) = {(p : Nat)} :=
  rfl

/--
theorem `coeNat_prime` / 定理 `coeNat_prime`

English:
theorem coeNat_prime
  given: (v : PrimeMultiset) (p : Nat) (h : p in (v : Multiset Nat))
  statement: p.Prime
  proof: by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

中文:
定理 coeNat_prime
  条件: (v : PrimeMultiset) (p : 自然数) (h : p in (v : Multiset 自然数))
  结论: p.Prime
  证明: by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

Depends on / 依赖: Multiset, Multiset.mem_map.mp, h_eq, mem_map
-/
theorem coeNat_prime (v : PrimeMultiset) (p : Nat) (h : p in (v : Multiset Nat)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

/--
Definition of `toPNatMultiset` / `toPNatMultiset` 的定义

English:
definition toPNatMultiset
  signature: : PrimeMultiset -> Multiset Nat+
  body: fun v => v.map (↑)

中文:
定义 toPNatMultiset
  签名: : PrimeMultiset -> Multiset 自然数+
  定义体: fun v => v.map (↑)

Depends on / 依赖: v.map
-/
def toPNatMultiset : PrimeMultiset -> Multiset Nat+ := fun v => v.map (↑)

/--
Instance `coePNat` / 实例 `coePNat`

English:
instance coePNat
  signature: : Coe PrimeMultiset (Multiset Nat+)
  body: ⟨toPNatMultiset⟩

中文:
实例 coePNat
  签名: : Coe PrimeMultiset (Multiset 自然数+)
  定义体: ⟨toPNatMultiset⟩

Depends on / 依赖: toPNatMultiset
-/
instance coePNat : Coe PrimeMultiset (Multiset Nat+) :=
  ⟨toPNatMultiset⟩

/--
Definition of `coePNatMonoidHom` / `coePNatMonoidHom` 的定义

English:
definition coePNatMonoidHom
  signature: : PrimeMultiset ->+ Multiset Nat+
  body: Multiset.mapAddMonoidHom (↑)

@[simp]

中文:
定义 coePNatMonoidHom
  签名: : PrimeMultiset ->+ Multiset 自然数+
  定义体: Multiset.mapAddMonoidHom (↑)

@[simp]

Depends on / 依赖: Multiset, Multiset.mapAddMonoidHom, mapAddMonoidHom
-/
def coePNatMonoidHom : PrimeMultiset ->+ Multiset Nat+ :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
/--
theorem `coe_coePNatMonoidHom` / 定理 `coe_coePNatMonoidHom`

English:
theorem coe_coePNatMonoidHom
  statement: (coePNatMonoidHom : PrimeMultiset -> Multiset Nat+) = (↑)
  proof: rfl

中文:
定理 coe_coePNatMonoidHom
  结论: (coeP自然数MonoidHom : PrimeMultiset -> Multiset 自然数+) = (↑)
  证明: rfl
-/
theorem coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset -> Multiset Nat+) = (↑) :=
  rfl

/--
theorem `coePNat_injective` / 定理 `coePNat_injective`

English:
theorem coePNat_injective
  statement: Function.Injective ((↑) : PrimeMultiset -> Multiset Nat+)
  proof: Multiset.map_injective Nat.Primes.coe_pnat_injective

中文:
定理 coePNat_injective
  结论: Function.Injective ((↑) : PrimeMultiset -> Multiset 自然数+)
  证明: Multiset.map_injective Nat.Primes.coe_pnat_injective

Depends on / 依赖: Multiset, Multiset.map_injective, Nat.Primes.coe_pnat_injective, Primes, coe_pnat_injective, map_injective
-/
theorem coePNat_injective : Function.Injective ((↑) : PrimeMultiset -> Multiset Nat+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective

/--
theorem `coePNat_ofPrime` / 定理 `coePNat_ofPrime`

English:
theorem coePNat_ofPrime
  given: (p : Nat.Primes)
  statement: (ofPrime p : Multiset Nat+) = {(p : Nat+)}
  proof: rfl

中文:
定理 coePNat_ofPrime
  条件: (p : 自然数.Primes)
  结论: (ofPrime p : Multiset 自然数+) = {(p : 自然数+)}
  证明: rfl
-/
theorem coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset Nat+) = {(p : Nat+)} :=
  rfl

/--
theorem `coePNat_prime` / 定理 `coePNat_prime`

English:
theorem coePNat_prime
  given: (v : PrimeMultiset) (p : Nat+) (h : p in (v : Multiset Nat+))
  statement: p.Prime
  proof: by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

中文:
定理 coePNat_prime
  条件: (v : PrimeMultiset) (p : 自然数+) (h : p in (v : Multiset 自然数+))
  结论: p.Prime
  证明: by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

Depends on / 依赖: Multiset, Multiset.mem_map.mp, h_eq, mem_map
-/
theorem coePNat_prime (v : PrimeMultiset) (p : Nat+) (h : p in (v : Multiset Nat+)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

/--
Instance `coeMultisetPNatNat` / 实例 `coeMultisetPNatNat`

English:
instance coeMultisetPNatNat
  signature: : Coe (Multiset Nat+) (Multiset Nat)
  body: ⟨fun v => v.map (↑)⟩

中文:
实例 coeMultisetPNatNat
  签名: : Coe (Multiset 自然数+) (Multiset 自然数)
  定义体: ⟨fun v => v.map (↑)⟩

Depends on / 依赖: v.map
-/
instance coeMultisetPNatNat : Coe (Multiset Nat+) (Multiset Nat) :=
  ⟨fun v => v.map (↑)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coePNat_nat` / 定理 `coePNat_nat`

English:
theorem coePNat_nat
  given: (v : PrimeMultiset)
  statement: ((v : Multiset Nat+) : Multiset Nat) = (v : Multiset Nat)
  proof: by
  change (v.map ((↑) : Nat.Primes -> Nat+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  rfl

中文:
定理 coePNat_nat
  条件: (v : PrimeMultiset)
  结论: ((v : Multiset 自然数+) : Multiset 自然数) = (v : Multiset 自然数)
  证明: by
  change (v.map ((↑) : Nat.Primes -> Nat+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  rfl

Depends on / 依赖: Multiset, Multiset.map_map, Nat.Primes, Primes, Subtype, Subtype.val, map_map, v.map
-/
theorem coePNat_nat (v : PrimeMultiset) : ((v : Multiset Nat+) : Multiset Nat) = (v : Multiset Nat) := by
  change (v.map ((↑) : Nat.Primes -> Nat+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  rfl

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (v : PrimeMultiset)
  body: (v : Multiset PNat).prod

中文:
定义 prod
  签名: (v : PrimeMultiset)
  定义体: (v : Multiset PNat).prod

Depends on / 依赖: Multiset
-/
def prod (v : PrimeMultiset) : Nat+ :=
  (v : Multiset PNat).prod

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (v : PrimeMultiset)
  statement: (v.prod : Nat) = (v : Multiset Nat).prod
  proof: by
  have h : (v.prod : Nat) = ((v.map (↑) : Multiset Nat+).map (↑)).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  simpa [Multiset.map_map] using! h

中文:
定理 coe_prod
  条件: (v : PrimeMultiset)
  结论: (v.prod : 自然数) = (v : Multiset 自然数).prod
  证明: by
  have h : (v.prod : Nat) = ((v.map (↑) : Multiset Nat+).map (↑)).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  simpa [Multiset.map_map] using! h

Depends on / 依赖: Multiset, Multiset.map_map, PNat.coeMonoidHom.map_multiset_prod, coeMonoidHom, map_map, map_multiset_prod, toPNatMultiset, v.map, v.prod, v.toPNatMultiset
-/
theorem coe_prod (v : PrimeMultiset) : (v.prod : Nat) = (v : Multiset Nat).prod := by
  have h : (v.prod : Nat) = ((v.map (↑) : Multiset Nat+).map (↑)).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  simpa [Multiset.map_map] using! h

/--
theorem `prod_ofPrime` / 定理 `prod_ofPrime`

English:
theorem prod_ofPrime
  given: (p : Nat.Primes)
  statement: (ofPrime p).prod = (p : Nat+)
  proof: Multiset.prod_singleton _

中文:
定理 prod_ofPrime
  条件: (p : 自然数.Primes)
  结论: (ofPrime p).prod = (p : 自然数+)
  证明: Multiset.prod_singleton _

Depends on / 依赖: Multiset, Multiset.prod_singleton, prod_singleton
-/
theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).prod = (p : Nat+) :=
  Multiset.prod_singleton _

/--
Definition of `ofNatMultiset` / `ofNatMultiset` 的定义

English:
definition ofNatMultiset
  signature: (v : Multiset Nat) (h : forall p : Nat, p in v -> p.Prime)
  body: @Multiset.pmap Nat Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

中文:
定义 ofNatMultiset
  签名: (v : Multiset 自然数) (h : 对任意 p : 自然数, p in v -> p.Prime)
  定义体: @Multiset.pmap Nat Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

Depends on / 依赖: Multiset, Multiset.pmap, Nat.Prime, Nat.Primes, Primes
-/
def ofNatMultiset (v : Multiset Nat) (h : forall p : Nat, p in v -> p.Prime) : PrimeMultiset :=
  @Multiset.pmap Nat Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_ofNatMultiset` / 定理 `mem_ofNatMultiset`

English:
theorem mem_ofNatMultiset
  given: {p : Nat+} {s : Multiset Nat} (hs)
  proof: by
  simp only [ofNatMultiset, toPNatMultiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat,
    ← PNat.coe_inj]
  simp

中文:
定理 mem_ofNatMultiset
  条件: {p : 自然数+} {s : Multiset 自然数} (hs)
  证明: by
  simp only [ofNatMultiset, toPNatMultiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat,
    ← PNat.coe_inj]
  simp

Depends on / 依赖: Multiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat, PNat.coe_inj, Primes, coe_inj, map_pmap, mem_pmap, ofNatMultiset, toPNat, toPNatMultiset
-/
theorem mem_ofNatMultiset {p : Nat+} {s : Multiset Nat} (hs) :
    p in (ofNatMultiset s hs : Multiset Nat+) ↔ (p : Nat) in s := by
  simp only [ofNatMultiset, toPNatMultiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat,
    ← PNat.coe_inj]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `to_ofNatMultiset` / 定理 `to_ofNatMultiset`

English:
theorem to_ofNatMultiset
  given: (v : Multiset Nat) (h)
  statement: (ofNatMultiset v h : Multiset Nat) = v
  proof: by
  dsimp [ofNatMultiset, toNatMultiset]
  rw [Multiset.map_pmap]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id']

@[simp]

中文:
定理 to_ofNatMultiset
  条件: (v : Multiset 自然数) (h)
  结论: (of自然数Multiset v h : Multiset 自然数) = v
  证明: by
  dsimp [ofNatMultiset, toNatMultiset]
  rw [Multiset.map_pmap]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id']

@[simp]

Depends on / 依赖: Multiset, Multiset.map_id, Multiset.map_pmap, Multiset.pmap_eq_map, map_id, map_pmap, ofNatMultiset, pmap_eq_map, toNatMultiset
-/
theorem to_ofNatMultiset (v : Multiset Nat) (h) : (ofNatMultiset v h : Multiset Nat) = v := by
  dsimp [ofNatMultiset, toNatMultiset]
  rw [Multiset.map_pmap]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id']

@[simp]
/--
theorem `prod_ofNatMultiset` / 定理 `prod_ofNatMultiset`

English:
theorem prod_ofNatMultiset
  given: (v : Multiset Nat) (h)
  proof: by rw [coe_prod, to_ofNatMultiset]

中文:
定理 prod_ofNatMultiset
  条件: (v : Multiset 自然数) (h)
  证明: by rw [coe_prod, to_ofNatMultiset]

Depends on / 依赖: coe_prod, to_ofNatMultiset
-/
theorem prod_ofNatMultiset (v : Multiset Nat) (h) :
    ((ofNatMultiset v h).prod : Nat) = (v.prod : Nat) := by rw [coe_prod, to_ofNatMultiset]

/--
Definition of `ofPNatMultiset` / `ofPNatMultiset` 的定义

English:
definition ofPNatMultiset
  signature: (v : Multiset Nat+) (h : forall p : Nat+, p in v -> p.Prime)
  body: @Multiset.pmap Nat+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : Nat), hp⟩) v h

中文:
定义 ofPNatMultiset
  签名: (v : Multiset 自然数+) (h : 对任意 p : 自然数+, p in v -> p.Prime)
  定义体: @Multiset.pmap Nat+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : Nat), hp⟩) v h

Depends on / 依赖: Multiset, Multiset.pmap, Nat.Primes, PNat.Prime, Primes
-/
def ofPNatMultiset (v : Multiset Nat+) (h : forall p : Nat+, p in v -> p.Prime) : PrimeMultiset :=
  @Multiset.pmap Nat+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : Nat), hp⟩) v h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `to_ofPNatMultiset` / 定理 `to_ofPNatMultiset`

English:
theorem to_ofPNatMultiset
  given: (v : Multiset Nat+) (h)
  statement: (ofPNatMultiset v h : Multiset Nat+) = v
  proof: by
  dsimp [ofPNatMultiset, toPNatMultiset]
  have : (fun (p : Nat+) (h : p.Prime) => ((↑) : Nat.Primes -> Nat+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.ext
    rfl
  rw [Multiset.map_pmap]; rw [this]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id]

@[simp]

中文:
定理 to_ofPNatMultiset
  条件: (v : Multiset 自然数+) (h)
  结论: (ofP自然数Multiset v h : Multiset 自然数+) = v
  证明: by
  dsimp [ofPNatMultiset, toPNatMultiset]
  have : (fun (p : Nat+) (h : p.Prime) => ((↑) : Nat.Primes -> Nat+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.ext
    rfl
  rw [Multiset.map_pmap]; rw [this]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_id, Multiset.map_pmap, Multiset.pmap_eq_map, Nat.Primes, Primes, Subtype, Subtype.ext, map_id, map_pmap, ofPNatMultiset, p.Prime, pmap_eq_map, toPNatMultiset
-/
theorem to_ofPNatMultiset (v : Multiset Nat+) (h) : (ofPNatMultiset v h : Multiset Nat+) = v := by
  dsimp [ofPNatMultiset, toPNatMultiset]
  have : (fun (p : Nat+) (h : p.Prime) => ((↑) : Nat.Primes -> Nat+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.ext
    rfl
  rw [Multiset.map_pmap]; rw [this]; rw [Multiset.pmap_eq_map]; rw [Multiset.map_id]

@[simp]
/--
theorem `prod_ofPNatMultiset` / 定理 `prod_ofPNatMultiset`

English:
theorem prod_ofPNatMultiset
  given: (v : Multiset Nat+) (h)
  statement: ((ofPNatMultiset v h).prod : Nat+) = v.prod
  proof: by
  dsimp [prod]
  rw [to_ofPNatMultiset]

中文:
定理 prod_ofPNatMultiset
  条件: (v : Multiset 自然数+) (h)
  结论: ((ofP自然数Multiset v h).prod : 自然数+) = v.prod
  证明: by
  dsimp [prod]
  rw [to_ofPNatMultiset]

Depends on / 依赖: to_ofPNatMultiset
-/
theorem prod_ofPNatMultiset (v : Multiset Nat+) (h) : ((ofPNatMultiset v h).prod : Nat+) = v.prod := by
  dsimp [prod]
  rw [to_ofPNatMultiset]

/--
Definition of `ofNatList` / `ofNatList` 的定义

English:
definition ofNatList
  signature: (l : List Nat) (h : forall p : Nat, p in l -> p.Prime)
  body: ofNatMultiset (l : Multiset Nat) h

中文:
定义 ofNatList
  签名: (l : List 自然数) (h : 对任意 p : 自然数, p in l -> p.Prime)
  定义体: ofNatMultiset (l : Multiset Nat) h

Depends on / 依赖: Multiset, ofNatMultiset
-/
def ofNatList (l : List Nat) (h : forall p : Nat, p in l -> p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset Nat) h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_ofNatList` / 定理 `mem_ofNatList`

English:
theorem mem_ofNatList
  given: {p : Nat+} {l : List Nat} (hl)
  proof: by
  simp [ofNatList]

@[simp]

中文:
定理 mem_ofNatList
  条件: {p : 自然数+} {l : List 自然数} (hl)
  证明: by
  simp [ofNatList]

@[simp]

Depends on / 依赖: Iff.rfl, ofNatList
-/
theorem mem_ofNatList {p : Nat+} {l : List Nat} (hl) :
    p in (ofNatList l hl : Multiset Nat+) ↔ (p : Nat) in l := by
  simp [ofNatList]

@[simp]
/--
theorem `prod_ofNatList` / 定理 `prod_ofNatList`

English:
theorem prod_ofNatList
  given: (l : List Nat) (h)
  statement: ((ofNatList l h).prod : Nat) = l.prod
  proof: by
  have := prod_ofNatMultiset (l : Multiset Nat) h
  rw [Multiset.prod_coe] at this
  exact this

中文:
定理 prod_ofNatList
  条件: (l : List 自然数) (h)
  结论: ((of自然数List l h).prod : 自然数) = l.prod
  证明: by
  have := prod_ofNatMultiset (l : Multiset Nat) h
  rw [Multiset.prod_coe] at this
  exact this

Depends on / 依赖: Multiset, Multiset.prod_coe, prod_coe, prod_ofNatMultiset
-/
theorem prod_ofNatList (l : List Nat) (h) : ((ofNatList l h).prod : Nat) = l.prod := by
  have := prod_ofNatMultiset (l : Multiset Nat) h
  rw [Multiset.prod_coe] at this
  exact this

/--
Definition of `ofPNatList` / `ofPNatList` 的定义

English:
definition ofPNatList
  signature: (l : List Nat+) (h : forall p : Nat+, p in l -> p.Prime)
  body: ofPNatMultiset (l : Multiset Nat+) h

中文:
定义 ofPNatList
  签名: (l : List 自然数+) (h : 对任意 p : 自然数+, p in l -> p.Prime)
  定义体: ofPNatMultiset (l : Multiset Nat+) h

Depends on / 依赖: Multiset, ofPNatMultiset
-/
def ofPNatList (l : List Nat+) (h : forall p : Nat+, p in l -> p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset Nat+) h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toPNatMultiset_ofPNatList` / 定理 `toPNatMultiset_ofPNatList`

English:
theorem toPNatMultiset_ofPNatList
  given: {l : List Nat+} (hl)
  statement: (ofPNatList l hl : Multiset Nat+) = l
  proof: by
  simp [ofPNatList]

@[simp]

中文:
定理 toPNatMultiset_ofPNatList
  条件: {l : List 自然数+} (hl)
  结论: (ofP自然数List l hl : Multiset 自然数+) = l
  证明: by
  simp [ofPNatList]

@[simp]

Depends on / 依赖: ofPNatList
-/
theorem toPNatMultiset_ofPNatList {l : List Nat+} (hl) : (ofPNatList l hl : Multiset Nat+) = l := by
  simp [ofPNatList]

@[simp]
/--
theorem `prod_ofPNatList` / 定理 `prod_ofPNatList`

English:
theorem prod_ofPNatList
  given: (l : List Nat+) (h)
  statement: (ofPNatList l h).prod = l.prod
  proof: by
  have := prod_ofPNatMultiset (l : Multiset Nat+) h
  rw [Multiset.prod_coe] at this
  exact this

中文:
定理 prod_ofPNatList
  条件: (l : List 自然数+) (h)
  结论: (ofP自然数List l h).prod = l.prod
  证明: by
  have := prod_ofPNatMultiset (l : Multiset Nat+) h
  rw [Multiset.prod_coe] at this
  exact this

Depends on / 依赖: Multiset, Multiset.prod_coe, NormedSpace, NormedSpace.toDiffeology, prod_coe, prod_ofPNatMultiset, toDiffeology
-/
theorem prod_ofPNatList (l : List Nat+) (h) : (ofPNatList l h).prod = l.prod := by
  have := prod_ofPNatMultiset (l : Multiset Nat+) h
  rw [Multiset.prod_coe] at this
  exact this

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
@[simp]
/--
theorem `prod_zero` / 定理 `prod_zero`

English:
theorem prod_zero
  statement: (0 : PrimeMultiset).prod = 1
  proof: by
  exact Multiset.prod_zero

@[simp]

中文:
定理 prod_zero
  结论: (0 : PrimeMultiset).prod = 1
  证明: by
  exact Multiset.prod_zero

@[simp]

Depends on / 依赖: Multiset, Multiset.prod_zero, prod_zero
-/
theorem prod_zero : (0 : PrimeMultiset).prod = 1 := by
  exact Multiset.prod_zero

@[simp]
/--
theorem `prod_add` / 定理 `prod_add`

English:
theorem prod_add
  given: (u v : PrimeMultiset)
  statement: (u + v).prod = u.prod * v.prod
  proof: by
  change (coePNatMonoidHom (u + v)).prod = _
  rw [coePNatMonoidHom.map_add]
  exact Multiset.prod_add _ _

@[simp]

中文:
定理 prod_add
  条件: (u v : PrimeMultiset)
  结论: (u + v).prod = u.prod * v.prod
  证明: by
  change (coePNatMonoidHom (u + v)).prod = _
  rw [coePNatMonoidHom.map_add]
  exact Multiset.prod_add _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.prod_add, coePNatMonoidHom, coePNatMonoidHom.map_add, map_add, prod_add
-/
theorem prod_add (u v : PrimeMultiset) : (u + v).prod = u.prod * v.prod := by
  change (coePNatMonoidHom (u + v)).prod = _
  rw [coePNatMonoidHom.map_add]
  exact Multiset.prod_add _ _

@[simp]
/--
theorem `prod_smul` / 定理 `prod_smul`

English:
theorem prod_smul
  given: (d : Nat) (u : PrimeMultiset)
  statement: (d • u).prod = u.prod ^ d
  proof: by
  induction d with
  | zero => simp only [zero_nsmul, pow_zero, prod_zero]
  | succ n ih => rw [succ_nsmul, prod_add, ih, pow_succ]

中文:
定理 prod_smul
  条件: (d : 自然数) (u : PrimeMultiset)
  结论: (d • u).prod = u.prod ^ d
  证明: by
  induction d with
  | zero => simp only [zero_nsmul, pow_zero, prod_zero]
  | succ n ih => rw [succ_nsmul, prod_add, ih, pow_succ]

Depends on / 依赖: pow_succ, pow_zero, prod_add, prod_zero, succ_nsmul, zero_nsmul
-/
theorem prod_smul (d : Nat) (u : PrimeMultiset) : (d • u).prod = u.prod ^ d := by
  induction d with
  | zero => simp only [zero_nsmul, pow_zero, prod_zero]
  | succ n ih => rw [succ_nsmul, prod_add, ih, pow_succ]

end PrimeMultiset

namespace PNat

/--
Definition of `factorMultiset` / `factorMultiset` 的定义

English:
definition factorMultiset
  signature: (n : Nat+)
  body: PrimeMultiset.ofNatList (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

中文:
定义 factorMultiset
  签名: (n : 自然数+)
  定义体: PrimeMultiset.ofNatList (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

Depends on / 依赖: Nat.primeFactorsList, Nat.prime_of_mem_primeFactorsList, PrimeMultiset, PrimeMultiset.ofNatList, ofNatList, primeFactorsList, prime_of_mem_primeFactorsList
-/
def factorMultiset (n : Nat+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

/-- The product of the factors is the original number -/
@[simp]
/--
theorem `prod_factorMultiset` / 定理 `prod_factorMultiset`

English:
theorem prod_factorMultiset
  given: (n : Nat+)
  statement: (factorMultiset n).prod = n
  proof: eq by
    dsimp [factorMultiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_primeFactorsList n.ne_zero

中文:
定理 prod_factorMultiset
  条件: (n : 自然数+)
  结论: (factorMultiset n).prod = n
  证明: eq by
    dsimp [factorMultiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_primeFactorsList n.ne_zero

Depends on / 依赖: Nat.prod_primeFactorsList, PrimeMultiset, PrimeMultiset.prod_ofNatList, factorMultiset, n.ne_zero, ne_zero, prod_ofNatList, prod_primeFactorsList
-/
theorem prod_factorMultiset (n : Nat+) : (factorMultiset n).prod = n :=
eq by
    dsimp [factorMultiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_primeFactorsList n.ne_zero

/--
theorem `coeNat_factorMultiset` / 定理 `coeNat_factorMultiset`

English:
theorem coeNat_factorMultiset
  given: (n : Nat+)
  proof: PrimeMultiset.to_ofNatMultiset (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

@[simp]

中文:
定理 coeNat_factorMultiset
  条件: (n : 自然数+)
  证明: PrimeMultiset.to_ofNatMultiset (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

@[simp]

Depends on / 依赖: Nat.primeFactorsList, Nat.prime_of_mem_primeFactorsList, PrimeMultiset, PrimeMultiset.to_ofNatMultiset, primeFactorsList, prime_of_mem_primeFactorsList, to_ofNatMultiset
-/
theorem coeNat_factorMultiset (n : Nat+) :
    (factorMultiset n : Multiset Nat) = (Nat.primeFactorsList n : Multiset Nat) :=
  PrimeMultiset.to_ofNatMultiset (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

@[simp]
/--
theorem `mem_factorMultiset` / 定理 `mem_factorMultiset`

English:
theorem mem_factorMultiset
  given: {p n : Nat+}
  statement: p in (n.factorMultiset : Multiset Nat+) ↔ p.Prime ∧ p ∣ n
  proof: by
  simp [factorMultiset, dvd_iff, PNat.Prime]

中文:
定理 mem_factorMultiset
  条件: {p n : 自然数+}
  结论: p in (n.factorMultiset : Multiset 自然数+) ↔ p.Prime ∧ p ∣ n
  证明: by
  simp [factorMultiset, dvd_iff, PNat.Prime]

Depends on / 依赖: PNat.Prime, dvd_iff, factorMultiset
-/
theorem mem_factorMultiset {p n : Nat+} : p in (n.factorMultiset : Multiset Nat+) ↔ p.Prime ∧ p ∣ n := by
  simp [factorMultiset, dvd_iff, PNat.Prime]

end PNat

namespace PrimeMultiset

set_option backward.isDefEq.respectTransparency false in
/-- If we start with a multiset of primes, take the product and
then factor it, we get back the original multiset. -/
@[simp]
/--
theorem `factorMultiset_prod` / 定理 `factorMultiset_prod`

English:
theorem factorMultiset_prod
  given: (v : PrimeMultiset)
  statement: v.prod.factorMultiset = v
  proof: by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coeNat_factorMultiset]; rw [PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  dsimp [PrimeMultiset.toNatMultiset]
  let l' := l.map ((↑) : Nat.Primes -> Nat)
  have (p : Nat) (hp : p in l') : p.Prime := by
    simp only [List.map_subtype, List.map_i

中文:
定理 factorMultiset_prod
  条件: (v : PrimeMultiset)
  结论: v.prod.factorMultiset = v
  证明: by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coeNat_factorMultiset]; rw [PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  dsimp [PrimeMultiset.toNatMultiset]
  let l' := l.map ((↑) : Nat.Primes -> Nat)
  have (p : Nat) (hp : p in l') : p.Prime := by
    simp only [List.map_subtype, List.map_i

Depends on / 依赖: List.map_id_fun, List.map_subtype, List.mem_unattach, Multiset, Multiset.coe_eq_coe.mpr, Nat.Primes, Nat.primeFactorsList_unique, PrimeMultiset, PrimeMultiset.coeNat_injective, PrimeMultiset.coe_prod, PrimeMultiset.toNatMultiset, Primes, coeNat_factorMultiset, coeNat_injective, coe_eq_coe, coe_prod, id_eq, l.map, map_id_fun, map_subtype
-/
theorem factorMultiset_prod (v : PrimeMultiset) : v.prod.factorMultiset = v := by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coeNat_factorMultiset]; rw [PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  dsimp [PrimeMultiset.toNatMultiset]
  let l' := l.map ((↑) : Nat.Primes -> Nat)
  have (p : Nat) (hp : p in l') : p.Prime := by
    simp only [List.map_subtype, List.map_id_fun', id_eq, List.mem_unattach, l'] at hp
    obtain ⟨hp', -⟩ := hp
    exact hp'
  exact Multiset.coe_eq_coe.mpr (@Nat.primeFactorsList_unique _ l' rfl this).symm

end PrimeMultiset

namespace PNat

/--
Definition of `factorMultisetEquiv` / `factorMultisetEquiv` 的定义

English:
definition factorMultisetEquiv
  signature: : Nat+ ≃ PrimeMultiset where
  body: factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod

中文:
定义 factorMultisetEquiv
  签名: : 自然数+ ≃ PrimeMultiset where
  定义体: factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod

Depends on / 依赖: factorMultiset
-/
def factorMultisetEquiv : Nat+ ≃ PrimeMultiset where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod

set_option backward.isDefEq.respectTransparency false in
/-- Factoring gives a homomorphism from the multiplicative
monoid ℕ+ to the additive monoid of multisets. -/
@[simp]
/--
theorem `factorMultiset_one` / 定理 `factorMultiset_one`

English:
theorem factorMultiset_one
  statement: factorMultiset 1 = 0
  proof: by
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

@[simp]

中文:
定理 factorMultiset_one
  结论: factorMultiset 1 = 0
  证明: by
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

@[simp]

Depends on / 依赖: PrimeMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset, factorMultiset, ofNatList, ofNatMultiset
-/
theorem factorMultiset_one : factorMultiset 1 = 0 := by
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

@[simp]
/--
theorem `factorMultiset_mul` / 定理 `factorMultiset_mul`

English:
theorem factorMultiset_mul
  given: (n m : Nat+)
  proof: by
  let u := factorMultiset n
  let v := factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

@[simp]

中文:
定理 factorMultiset_mul
  条件: (n m : 自然数+)
  证明: by
  let u := factorMultiset n
  let v := factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

@[simp]

Depends on / 依赖: PrimeMultiset, PrimeMultiset.factorMultiset_prod, PrimeMultiset.prod_add, factorMultiset, factorMultiset_prod, prod_add, prod_factorMultiset, repeat, u.prod, v.prod
-/
theorem factorMultiset_mul (n m : Nat+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m := by
  let u := factorMultiset n
  let v := factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

@[simp]
/--
theorem `factorMultiset_pow` / 定理 `factorMultiset_pow`

English:
theorem factorMultiset_pow
  given: (n : Nat+) (m : Nat)
  proof: by
  let u := factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  rw [this]; rw [← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

中文:
定理 factorMultiset_pow
  条件: (n : 自然数+) (m : 自然数)
  证明: by
  let u := factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  rw [this]; rw [← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

Depends on / 依赖: PrimeMultiset, PrimeMultiset.factorMultiset_prod, PrimeMultiset.prod_smul, factorMultiset, factorMultiset_prod, prod_factorMultiset, prod_smul, repeat, u.prod
-/
theorem factorMultiset_pow (n : Nat+) (m : Nat) :
    factorMultiset (n ^ m) = m • factorMultiset n := by
  let u := factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  rw [this]; rw [← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

/--
theorem `factorMultiset_ofPrime` / 定理 `factorMultiset_ofPrime`

English:
theorem factorMultiset_ofPrime
  given: (p : Nat.Primes)
  proof: by
  apply factorMultisetEquiv.symm.injective
  change (p : Nat+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  rw [(p : Nat+).prod_factorMultiset]; rw [PrimeMultiset.prod_ofPrime]

中文:
定理 factorMultiset_ofPrime
  条件: (p : 自然数.Primes)
  证明: by
  apply factorMultisetEquiv.symm.injective
  change (p : Nat+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  rw [(p : Nat+).prod_factorMultiset]; rw [PrimeMultiset.prod_ofPrime]

Depends on / 依赖: PrimeMultiset, PrimeMultiset.ofPrime, PrimeMultiset.prod_ofPrime, factorMultiset, factorMultiset.prod, factorMultisetEquiv, factorMultisetEquiv.symm.injective, injective, ofPrime, prod_factorMultiset, prod_ofPrime
-/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : Nat+).factorMultiset = PrimeMultiset.ofPrime p := by
  apply factorMultisetEquiv.symm.injective
  change (p : Nat+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  rw [(p : Nat+).prod_factorMultiset]; rw [PrimeMultiset.prod_ofPrime]

/-- We now have four different results that all encode the
idea that inequality of multisets corresponds to divisibility
of positive integers. -/
@[simp]
/--
theorem `factorMultiset_le_iff` / 定理 `factorMultiset_le_iff`

English:
theorem factorMultiset_le_iff
  given: {m n : Nat+}
  statement: factorMultiset m <= factorMultiset n ↔ m ∣ n
  proof: by
  constructor
  · intro h
    rw [← prod_factorMultiset m]; rw [← prod_factorMultiset m]
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    rw [← PrimeMultiset.prod_add]; rw [PrimeMultiset.factorMultiset_prod]; rw [add_tsub_cancel_of_le h]; rw [prod_factorMultiset]
  · intro h
   

中文:
定理 factorMultiset_le_iff
  条件: {m n : 自然数+}
  结论: factorMultiset m <= factorMultiset n ↔ m ∣ n
  证明: by
  constructor
  · intro h
    rw [← prod_factorMultiset m]; rw [← prod_factorMultiset m]
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    rw [← PrimeMultiset.prod_add]; rw [PrimeMultiset.factorMultiset_prod]; rw [add_tsub_cancel_of_le h]; rw [prod_factorMultiset]
  · intro h
   

Depends on / 依赖: Dvd.intro, PrimeMultiset, PrimeMultiset.factorMultiset_prod, PrimeMultiset.prod_add, add_tsub_cancel_of_le, factorMultiset, factorMultiset_mul, factorMultiset_prod, le_self_add, m.factorMultiset, mul_div_exact, n.factorMultiset, prod_add, prod_factorMultiset
-/
theorem factorMultiset_le_iff {m n : Nat+} : factorMultiset m <= factorMultiset n ↔ m ∣ n := by
  constructor
  · intro h
    rw [← prod_factorMultiset m]; rw [← prod_factorMultiset m]
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    rw [← PrimeMultiset.prod_add]; rw [PrimeMultiset.factorMultiset_prod]; rw [add_tsub_cancel_of_le h]; rw [prod_factorMultiset]
  · intro h
    rw [← mul_div_exact h]; rw [factorMultiset_mul]
    exact le_self_add

@[gcongr]
alias ⟨_, factorMultiset_mono⟩ := factorMultiset_le_iff

/--
theorem `factorMultiset_le_iff'` / 定理 `factorMultiset_le_iff'`

English:
theorem factorMultiset_le_iff'
  given: {m : Nat+} {v : PrimeMultiset}
  proof: by
  let h := @factorMultiset_le_iff m v.prod
  rw [v.factorMultiset_prod] at h
  exact h

中文:
定理 factorMultiset_le_iff'
  条件: {m : 自然数+} {v : PrimeMultiset}
  证明: by
  let h := @factorMultiset_le_iff m v.prod
  rw [v.factorMultiset_prod] at h
  exact h

Depends on / 依赖: factorMultiset_le_iff, factorMultiset_prod, v.factorMultiset_prod, v.prod
-/
theorem factorMultiset_le_iff' {m : Nat+} {v : PrimeMultiset} :
    factorMultiset m <= v ↔ m ∣ v.prod := by
  let h := @factorMultiset_le_iff m v.prod
  rw [v.factorMultiset_prod] at h
  exact h

end PNat

namespace PrimeMultiset

@[simp]
/--
theorem `prod_dvd_iff` / 定理 `prod_dvd_iff`

English:
theorem prod_dvd_iff
  given: {u v : PrimeMultiset}
  statement: u.prod ∣ v.prod ↔ u <= v
  proof: by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factorMultiset_prod] at h
  exact h.symm

@[gcongr] alias ⟨_, prod_dvd_prod⟩ := prod_dvd_iff

中文:
定理 prod_dvd_iff
  条件: {u v : PrimeMultiset}
  结论: u.prod ∣ v.prod ↔ u <= v
  证明: by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factorMultiset_prod] at h
  exact h.symm

@[gcongr] alias ⟨_, prod_dvd_prod⟩ := prod_dvd_iff

Depends on / 依赖: PNat.factorMultiset_le_iff, factorMultiset_le_iff, factorMultiset_prod, h.symm, u.factorMultiset_prod, u.prod
-/
theorem prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u <= v := by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factorMultiset_prod] at h
  exact h.symm

@[gcongr] alias ⟨_, prod_dvd_prod⟩ := prod_dvd_iff

/--
theorem `prod_dvd_iff'` / 定理 `prod_dvd_iff'`

English:
theorem prod_dvd_iff'
  given: {u : PrimeMultiset} {n : Nat+}
  statement: u.prod ∣ n ↔ u <= n.factorMultiset
  proof: by
  let h := @prod_dvd_iff u n.factorMultiset
  rw [n.prod_factorMultiset] at h
  exact h

中文:
定理 prod_dvd_iff'
  条件: {u : PrimeMultiset} {n : 自然数+}
  结论: u.prod ∣ n ↔ u <= n.factorMultiset
  证明: by
  let h := @prod_dvd_iff u n.factorMultiset
  rw [n.prod_factorMultiset] at h
  exact h

Depends on / 依赖: factorMultiset, n.factorMultiset, n.prod_factorMultiset, prod_dvd_iff, prod_factorMultiset
-/
theorem prod_dvd_iff' {u : PrimeMultiset} {n : Nat+} : u.prod ∣ n ↔ u <= n.factorMultiset := by
  let h := @prod_dvd_iff u n.factorMultiset
  rw [n.prod_factorMultiset] at h
  exact h

end PrimeMultiset

namespace PNat

/--
theorem `factorMultiset_gcd` / 定理 `factorMultiset_gcd`

English:
theorem factorMultiset_gcd
  given: (m n : Nat+)
  proof: by
  apply le_antisymm
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact gcd_dvd_left m n
    · exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    · exact inf_le_left
    · 

中文:
定理 factorMultiset_gcd
  条件: (m n : 自然数+)
  证明: by
  apply le_antisymm
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact gcd_dvd_left m n
    · exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    · exact inf_le_left
    · 

Depends on / 依赖: PrimeMultiset, PrimeMultiset.prod_dvd_iff, dvd_gcd, factorMultiset_le_iff, factorMultiset_le_iff.mpr, gcd_dvd_left, gcd_dvd_right, inf_le_left, inf_le_right, le_antisymm, le_inf_iff, le_inf_iff.mpr, prod_dvd_iff, prod_factorMultiset
-/
theorem factorMultiset_gcd (m n : Nat+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n := by
  apply le_antisymm
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact gcd_dvd_left m n
    · exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    · exact inf_le_left
    · exact inf_le_right

/--
theorem `factorMultiset_lcm` / 定理 `factorMultiset_lcm`

English:
theorem factorMultiset_lcm
  given: (m n : Nat+)
  proof: by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply lcm_dvd <;> rw [← factorMultiset_le_iff']
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact dvd_lcm_left m n
    · exact dv

中文:
定理 factorMultiset_lcm
  条件: (m n : 自然数+)
  证明: by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply lcm_dvd <;> rw [← factorMultiset_le_iff']
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact dvd_lcm_left m n
    · exact dv

Depends on / 依赖: PrimeMultiset, PrimeMultiset.prod_dvd_iff, dvd_lcm_left, dvd_lcm_right, factorMultiset_le_iff, factorMultiset_le_iff.mpr, lcm_dvd, le_antisymm, le_sup_left, le_sup_right, prod_dvd_iff, prod_factorMultiset, sup_le_iff, sup_le_iff.mpr
-/
theorem factorMultiset_lcm (m n : Nat+) :
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
/--
theorem `count_factorMultiset` / 定理 `count_factorMultiset`

English:
theorem count_factorMultiset
  given: (m : Nat+) (p : Nat.Primes) (k : Nat)
  proof: by
  rw [Multiset.le_count_iff_replicate_le]; rw [← factorMultiset_le_iff]; rw [factorMultiset_pow]; rw [factorMultiset_ofPrime]
  congr! 2
  apply Multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime]; 

中文:
定理 count_factorMultiset
  条件: (m : 自然数+) (p : 自然数.Primes) (k : 自然数)
  证明: by
  rw [Multiset.le_count_iff_replicate_le]; rw [← factorMultiset_le_iff]; rw [factorMultiset_pow]; rw [factorMultiset_ofPrime]
  congr! 2
  apply Multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime]; 

Depends on / 依赖: Multiset, Multiset.card_nsmul, Multiset.eq_of_mem_replicate, Multiset.eq_replicate.mpr, Multiset.le_count_iff_replicate_le, Multiset.nsmul_singleton, PrimeMultiset, PrimeMultiset.card_ofPrime, PrimeMultiset.ofPrime, card_nsmul, card_ofPrime, eq_of_mem_replicate, eq_replicate, factorMultiset_le_iff, factorMultiset_ofPrime, factorMultiset_pow, le_count_iff_replicate_le, mul_one, nsmul_singleton, ofPrime
-/
theorem count_factorMultiset (m : Nat+) (p : Nat.Primes) (k : Nat) :
    (p : Nat+) ^ k ∣ m ↔ k <= m.factorMultiset.count p := by
  rw [Multiset.le_count_iff_replicate_le]; rw [← factorMultiset_le_iff]; rw [factorMultiset_pow]; rw [factorMultiset_ofPrime]
  congr! 2
  apply Multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime]; rw [Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_replicate h

end PNat

namespace PrimeMultiset

/--
theorem `prod_inf` / 定理 `prod_inf`

English:
theorem prod_inf
  given: (u v : PrimeMultiset)
  statement: (u ⊓ v).prod = PNat.gcd u.prod v.prod
  proof: by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).prod = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m]; rw [PNat.prod_factorMultiset]

中文:
定理 prod_inf
  条件: (u v : PrimeMultiset)
  结论: (u ⊓ v).prod = P自然数.gcd u.prod v.prod
  证明: by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).prod = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m]; rw [PNat.prod_factorMultiset]

Depends on / 依赖: PNat.factorMultiset_gcd, PNat.gcd, PNat.prod_factorMultiset, factorMultiset, factorMultiset_gcd, factorMultiset_prod, m.factorMultiset, n.factorMultiset, prod_factorMultiset, u.factorMultiset_prod.symm, u.prod, v.factorMultiset_prod.symm, v.prod
-/
theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).prod = PNat.gcd u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).prod = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m]; rw [PNat.prod_factorMultiset]

/--
theorem `prod_sup` / 定理 `prod_sup`

English:
theorem prod_sup
  given: (u v : PrimeMultiset)
  statement: (u ⊔ v).prod = PNat.lcm u.prod v.prod
  proof: by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).prod = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m]; rw [PNat.prod_factorMultiset]

中文:
定理 prod_sup
  条件: (u v : PrimeMultiset)
  结论: (u ⊔ v).prod = P自然数.lcm u.prod v.prod
  证明: by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).prod = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m]; rw [PNat.prod_factorMultiset]

Depends on / 依赖: PNat.factorMultiset_lcm, PNat.lcm, PNat.prod_factorMultiset, factorMultiset, factorMultiset_lcm, factorMultiset_prod, m.factorMultiset, n.factorMultiset, prod_factorMultiset, u.factorMultiset_prod.symm, u.prod, v.factorMultiset_prod.symm, v.prod
-/
theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).prod = PNat.lcm u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).prod = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m]; rw [PNat.prod_factorMultiset]

end PrimeMultiset
