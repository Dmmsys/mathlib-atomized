/-
Copyright (c) 2023 Hanneke Wiersema. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Hanneke Wiersema, Andrew Yang
-/
module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.FieldTheory.KrullTopology

/-!

# The cyclotomic character

Let `L` be an integral domain and let `n : ℕ+` be a positive integer. If `μₙ` is the
group of `n`th roots of unity in `L` then any field automorphism `g` of `L`
induces an automorphism of `μₙ` which, being a cyclic group, must be of
the form `ζ ↦ ζ^j` for some integer `j = j(g)`, well-defined in `ZMod d`, with
`d` the cardinality of `μₙ`. The function `j` is a group homomorphism
`(L ≃+* L) →* ZMod d`.

Future work: If `L` is separably closed (e.g. algebraically closed) and `p` is a prime
number such that `p ≠ 0` in `L`, then applying the above construction with
`n = p^i` (noting that the size of `μₙ` is `p^i`) gives a compatible collection of
group homomorphisms `(L ≃+* L) →* ZMod (p^i)` which glue to give
a group homomorphism `(L ≃+* L) →* ℤₚ`; this is the `p`-adic cyclotomic character.

## Important definitions

Let `L` be an integral domain, `g : L ≃+* L` and `n : ℕ+`. Let `d` be the number of `n`th roots
of `1` in `L`.

* `modularCyclotomicCharacter L n hn : (L ≃+* L) →* (ZMod n)ˣ` sends `g` to the unique `j` such
  that `g(ζ)=ζ^j` for all `ζ : rootsOfUnity n L`. Here `hn` is a proof that there
  are `n` `n`th roots of unity in `L`.

* `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ` sends `g` to the unique `j` such
  that `g(ζ) = ζ ^ (j mod pⁱ)` for all `pⁱ`-th roots of unity `ζ`.

  Note: This is defined to be the trivial character if `L` does not have enough roots of unity.

## Implementation note

In theory this could be set up as some theory about monoids, being a character
on monoid isomorphisms, but under the hypotheses that the `n`-th roots of unity
are cyclic. The advantage of sticking to integral domains is that finite subgroups
are guaranteed to be cyclic, so the weaker assumption that there are `n` `n`th
roots of unity is enough. All the applications I'm aware of are when `L` is a
field anyway.

Although I don't know whether it's of any use, `modularCyclotomicCharacter'`
is the general case for integral domains, with target in `(ZMod d)ˣ`
where `d` is the number of `n`th roots of unity in `L`.

## TODO

* Prove the compatibility of `modularCyclotomicCharacter n` and `modularCyclotomicCharacter m`
  if `n ∣ m`.

## Tags

cyclotomic character
-/

@[expose] public section

universe u
variable {L : Type u} [CommRing L] [IsDomain L]

/-

## The mod n theory

-/

variable (n : Nat) [NeZero n]

/--
theorem `rootsOfUnity.integer_power_of_ringEquiv` / 定理 `rootsOfUnity.integer_power_of_ringEquiv`

English:
theorem rootsOfUnity.integer_power_of_ringEquiv
  given: (g : L ≃+* L)
  proof: by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
exact ⟨m, fun t => Units.ext_iff.1 SetCoe.ext_iff.2 hm t⟩

中文:
定理 rootsOfUnity.integer_power_of_ringEquiv
  条件: (g : L ≃+* L)
  证明: by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
exact ⟨m, fun t => Units.ext_iff.1 SetCoe.ext_iff.2 hm t⟩

Depends on / 依赖: MonoidHom, MonoidHom.map_cyclic, SetCoe, SetCoe.ext_iff, Units.ext_iff, ext_iff, map_cyclic, restrictRootsOfUnity, toMonoidHom
-/
theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    exists m : Int, forall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
exact ⟨m, fun t => Units.ext_iff.1 SetCoe.ext_iff.2 hm t⟩

/--
theorem `rootsOfUnity.integer_power_of_ringEquiv'` / 定理 `rootsOfUnity.integer_power_of_ringEquiv'`

English:
theorem rootsOfUnity.integer_power_of_ringEquiv'
  given: (g : L ≃+* L)
  proof: by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

中文:
定理 rootsOfUnity.integer_power_of_ringEquiv'
  条件: (g : L ≃+* L)
  证明: by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

Depends on / 依赖: integer_power_of_ringEquiv, rootsOfUnity, rootsOfUnity.integer_power_of_ringEquiv
-/
theorem rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) :
    exists m : Int, forall t in rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

/--
Definition of `modularCyclotomicCharacter.aux` / `modularCyclotomicCharacter.aux` 的定义

English:
definition modularCyclotomicCharacter.aux
  signature: (g : L ≃+* L) (n : Nat) [NeZero n]
  body: (rootsOfUnity.integer_power_of_ringEquiv n g).choose

中文:
定义 modularCyclotomicCharacter.aux
  签名: (g : L ≃+* L) (n : 自然数) [NeZero n]
  定义体: (rootsOfUnity.integer_power_of_ringEquiv n g).choose

Depends on / 依赖: integer_power_of_ringEquiv, rootsOfUnity, rootsOfUnity.integer_power_of_ringEquiv
-/
noncomputable def modularCyclotomicCharacter.aux (g : L ≃+* L) (n : Nat) [NeZero n] : Int :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose

-- the only thing we know about `modularCyclotomicCharacter_aux g n`
/--
theorem `modularCyclotomicCharacter.aux_spec` / 定理 `modularCyclotomicCharacter.aux_spec`

English:
theorem modularCyclotomicCharacter.aux_spec
  given: (g : L ≃+* L) (n : Nat) [NeZero n]
  proof: (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

中文:
定理 modularCyclotomicCharacter.aux_spec
  条件: (g : L ≃+* L) (n : 自然数) [NeZero n]
  证明: (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

Depends on / 依赖: choose_spec, integer_power_of_ringEquiv, rootsOfUnity, rootsOfUnity.integer_power_of_ringEquiv
-/
theorem modularCyclotomicCharacter.aux_spec (g : L ≃+* L) (n : Nat) [NeZero n] :
    forall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (modularCyclotomicCharacter.aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

/--
theorem `modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow` / 定理 `modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow`

English:
theorem modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow
  proof: by
  obtain ⟨i, rfl⟩ := exists_add_of_le hi
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ (k + i))
  have h := hζ.pow (a := p ^ i) (Nat.pos_of_neZero _) (Nat.pow_add' _ _ _)
  have h_unit : (h.isUnit NeZero.out).unit =
      (hζ.isUnit NeZero.out).unit ^ (p ^ i) := by ext; rf

中文:
定理 modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow
  证明: by
  obtain ⟨i, rfl⟩ := exists_add_of_le hi
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ (k + i))
  have h := hζ.pow (a := p ^ i) (Nat.pos_of_neZero _) (Nat.pow_add' _ _ _)
  have h_unit : (h.isUnit NeZero.out).unit =
      (hζ.isUnit NeZero.out).unit ^ (p ^ i) := by ext; rf

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.exists_primitiveRoot, IsUnit, IsUnit.unit_spec, Nat.pos_of_neZero, Nat.pow_add, NeZero, NeZero.out, aux_spec, exists_add_of_le, exists_primitiveRoot, h.isUnit, h.isUnit_unit, h_unit, isUnit, isUnit_unit, map_pow, mem_rootsOfUnity, pos_of_neZero, pow_add
-/
theorem modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow
    (g : L ≃+* L) (p : Nat) [Fact p.Prime] [forall i, HasEnoughRootsOfUnity L (p ^ i)]
    {i k : Nat} (hi : k <= i) : (p : Int) ^ k ∣ aux g (p ^ i) - aux g (p ^ k) := by
  obtain ⟨i, rfl⟩ := exists_add_of_le hi
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ (k + i))
  have h := hζ.pow (a := p ^ i) (Nat.pos_of_neZero _) (Nat.pow_add' _ _ _)
  have h_unit : (h.isUnit NeZero.out).unit =
      (hζ.isUnit NeZero.out).unit ^ (p ^ i) := by ext; rfl
  have H₁ := aux_spec g (p ^ (k + i))
    ⟨_, (hζ.isUnit_unit NeZero.out).mem_rootsOfUnity⟩
  have H₂ := aux_spec g (p ^ k)
    ⟨_, (h.isUnit_unit NeZero.out).mem_rootsOfUnity⟩
  simp only [IsUnit.unit_spec, map_pow] at H₁ H₂
  rw [H₁]; rw [← Units.val_pow_eq_pow_val]; rw [← Units.ext_iff]; rw [h_unit]; rw [← div_eq_one] at H₂
  simp only [← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_sub] at H₂
  rw [(hζ.isUnit_unit NeZero.out).zpow_eq_one_iff_dvd]; rw [mul_comm]; rw [← mul_sub] at H₂
  conv_lhs at H₂ => rw [Nat.pow_add', Nat.cast_mul]
  rwa [mul_dvd_mul_iff_left (by simp [NeZero.ne p]), Nat.cast_pow] at H₂

/--
Definition of `modularCyclotomicCharacter.toFun` / `modularCyclotomicCharacter.toFun` 的定义

English:
definition modularCyclotomicCharacter.toFun
  signature: (n : Nat) [NeZero n] (g : L ≃+* L)
  body: modularCyclotomicCharacter.aux g n

中文:
定义 modularCyclotomicCharacter.toFun
  签名: (n : 自然数) [NeZero n] (g : L ≃+* L)
  定义体: modularCyclotomicCharacter.aux g n

Depends on / 依赖: modularCyclotomicCharacter, modularCyclotomicCharacter.aux
-/
noncomputable def modularCyclotomicCharacter.toFun (n : Nat) [NeZero n] (g : L ≃+* L) :
    ZMod (Nat.card (rootsOfUnity n L)) :=
  modularCyclotomicCharacter.aux g n

namespace modularCyclotomicCharacter

local notation "χ₀" => modularCyclotomicCharacter.toFun

/--
theorem `toFun_spec` / 定理 `toFun_spec`

English:
theorem toFun_spec
  given: (g : L ≃+* L) {n : Nat} [NeZero n] (t : rootsOfUnity n L)
  proof: by
  rw [modularCyclotomicCharacter.aux_spec g n t]; rw [← zpow_natCast]; rw [modularCyclotomicCharacter.toFun]; rw [ZMod.val_intCast]; rw [← Subgroup.coe_zpow]
exact Units.ext_iff.1 SetCoe.ext_iff.2
    zpow_eq_zpow_emod _ pow_card_eq_one' (G := rootsOfUnity n L)

中文:
定理 toFun_spec
  条件: (g : L ≃+* L) {n : 自然数} [NeZero n] (t : rootsOfUnity n L)
  证明: by
  rw [modularCyclotomicCharacter.aux_spec g n t]; rw [← zpow_natCast]; rw [modularCyclotomicCharacter.toFun]; rw [ZMod.val_intCast]; rw [← Subgroup.coe_zpow]
exact Units.ext_iff.1 SetCoe.ext_iff.2
    zpow_eq_zpow_emod _ pow_card_eq_one' (G := rootsOfUnity n L)

Depends on / 依赖: SetCoe, SetCoe.ext_iff, Subgroup, Subgroup.coe_zpow, Units.ext_iff, ZMod.val_intCast, aux_spec, coe_zpow, ext_iff, modularCyclotomicCharacter, modularCyclotomicCharacter.aux_spec, modularCyclotomicCharacter.toFun, pow_card_eq_one, rootsOfUnity, val_intCast, zpow_eq_zpow_emod, zpow_natCast
-/
theorem toFun_spec (g : L ≃+* L) {n : Nat} [NeZero n] (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ) := by
  rw [modularCyclotomicCharacter.aux_spec g n t]; rw [← zpow_natCast]; rw [modularCyclotomicCharacter.toFun]; rw [ZMod.val_intCast]; rw [← Subgroup.coe_zpow]
exact Units.ext_iff.1 SetCoe.ext_iff.2
    zpow_eq_zpow_emod _ pow_card_eq_one' (G := rootsOfUnity n L)

/--
theorem `toFun_spec'` / 定理 `toFun_spec'`

English:
theorem toFun_spec'
  given: (g : L ≃+* L) {n : Nat} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L)
  proof: toFun_spec g ⟨t, ht⟩

中文:
定理 toFun_spec'
  条件: (g : L ≃+* L) {n : 自然数} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L)
  证明: toFun_spec g ⟨t, ht⟩

Depends on / 依赖: toFun_spec
-/
theorem toFun_spec' (g : L ≃+* L) {n : Nat} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec g ⟨t, ht⟩

/--
theorem `toFun_spec''` / 定理 `toFun_spec''`

English:
theorem toFun_spec''
  given: (g : L ≃+* L) {n : Nat} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n)
  proof: toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

中文:
定理 toFun_spec''
  条件: (g : L ≃+* L) {n : 自然数} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n)
  证明: toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, ht.toRootsOfUnity, toFun_spec, toRootsOfUnity
-/
theorem toFun_spec'' (g : L ≃+* L) {n : Nat} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

/--
theorem `toFun_unique` / 定理 `toFun_unique`

English:
theorem toFun_unique
  statement: (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
  proof: by
  apply IsCyclic.ext rfl (fun ζ => ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ]; rw [hc]

中文:
定理 toFun_unique
  结论: (g : L ≃+* L) (c : ZMod (自然数.card (rootsOfUnity n L)))
  证明: by
  apply IsCyclic.ext rfl (fun ζ => ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ]; rw [hc]

Depends on / 依赖: IsCyclic, IsCyclic.ext, c.val, specialize, toFun_spec
-/
theorem toFun_unique (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
    (hc : forall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext rfl (fun ζ => ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ]; rw [hc]

/--
theorem `toFun_unique'` / 定理 `toFun_unique'`

English:
theorem toFun_unique'
  statement: (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
  proof: toFun_unique n g c (fun ⟨_, ht⟩ => hc _ ht)

中文:
定理 toFun_unique'
  结论: (g : L ≃+* L) (c : ZMod (自然数.card (rootsOfUnity n L)))
  证明: toFun_unique n g c (fun ⟨_, ht⟩ => hc _ ht)

Depends on / 依赖: toFun_unique
-/
theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
    (hc : forall t in rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ => hc _ ht)

/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: χ₀ n (RingEquiv.refl L) = 1
  proof: by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t => ?_).symm
  have : 1 <= Nat.card { x // x in rootsOfUnity n L } := Nat.card_pos
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Finite.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 :

中文:
引理 id
  结论: χ₀ n (RingEquiv.refl L) = 1
  证明: by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t => ?_).symm
  have : 1 <= Nat.card { x // x in rootsOfUnity n L } := Nat.card_pos
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Finite.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 :

Depends on / 依赖: Fact.mk, Finite, Finite.card_le_one_iff_subsingleton.mp, Nat.card, Nat.card_pos, RingEquiv, RingEquiv.refl, Subsingleton, Subsingleton.elim, ZMod.val_one, card_le_one_iff_subsingleton, card_pos, h.ge, lt_or_eq, rootsOfUnity, this.lt_or_eq, toFun_unique, val_one
-/
lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t => ?_).symm
  have : 1 <= Nat.card { x // x in rootsOfUnity n L } := Nat.card_pos
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Finite.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (g h : L ≃+* L)
  statement: χ₀ n (g * h) =
  proof: by
  refine (toFun_unique n (g * h) _ <| fun ζ => ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec]; rw [← Subgroup.coe_pow]; rw [toFun_spec]; rw [mul_comm]; rw [Subgroup.coe_pow]; rw [← pow_mul]; rw [← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq

中文:
引理 comp
  条件: (g h : L ≃+* L)
  结论: χ₀ n (g * h) =
  证明: by
  refine (toFun_unique n (g * h) _ <| fun ζ => ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec]; rw [← Subgroup.coe_pow]; rw [toFun_spec]; rw [mul_comm]; rw [Subgroup.coe_pow]; rw [← pow_mul]; rw [← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq

Depends on / 依赖: Nat.cast_mul, Subgroup, Subgroup.coe_pow, ZMod.cast_mul, ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, cast_mul, coe_pow, mul_comm, natCast_eq_natCast_iff, natCast_val, orderOf, orderOf_dvd_natCard, pow_eq_pow_iff_modEq, pow_mul, toFun_spec, toFun_unique
-/
lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
    χ₀ n g * χ₀ n h := by
  refine (toFun_unique n (g * h) _ <| fun ζ => ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec]; rw [← Subgroup.coe_pow]; rw [toFun_spec]; rw [mul_comm]; rw [Subgroup.coe_pow]; rw [← pow_mul]; rw [← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) (orderOf_dvd_natCard _)]

end modularCyclotomicCharacter

variable (L)

/-- Given a positive integer `n`, `modularCyclotomicCharacter' n` is a
multiplicative homomorphism from the automorphisms of a field `L` to `(ℤ/dℤ)ˣ`,
where `d` is the number of `n`-th roots of unity in `L`. It is uniquely
characterised by the property that `g(ζ)=ζ^(modularCyclotomicCharacter n g)`
for `g` an automorphism of `L` and `ζ` an `n`th root of unity. -/
noncomputable
/--
Definition of `modularCyclotomicCharacter'` / `modularCyclotomicCharacter'` 的定义

English:
definition modularCyclotomicCharacter'
  signature: (n : Nat) [NeZero n]
  body: MonoidHom.toHomUnits
  { toFun := modularCyclotomicCharacter.toFun n
    map_one' := modularCyclotomicCharacter.id n
    map_mul' := modularCyclotomicCharacter.comp n }

中文:
定义 modularCyclotomicCharacter'
  签名: (n : 自然数) [NeZero n]
  定义体: MonoidHom.toHomUnits
  { toFun := modularCyclotomicCharacter.toFun n
    map_one' := modularCyclotomicCharacter.id n
    map_mul' := modularCyclotomicCharacter.comp n }

Depends on / 依赖: MonoidHom, MonoidHom.toHomUnits, toHomUnits
-/
def modularCyclotomicCharacter' (n : Nat) [NeZero n] :
    (L ≃+* L) ->* (ZMod (Nat.card { x // x in rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := modularCyclotomicCharacter.toFun n
    map_one' := modularCyclotomicCharacter.id n
    map_mul' := modularCyclotomicCharacter.comp n }

/--
lemma `modularCyclotomicCharacter'.spec'` / 引理 `modularCyclotomicCharacter'.spec'`

English:
lemma modularCyclotomicCharacter'.spec'
  given: (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L)
  proof: modularCyclotomicCharacter.toFun_spec' g ht

中文:
引理 modularCyclotomicCharacter'.spec'
  条件: (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L)
  证明: modularCyclotomicCharacter.toFun_spec' g ht
-/
lemma modularCyclotomicCharacter'.spec' (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L) :
    g t = t ^ ((modularCyclotomicCharacter' L n g) : ZMod
      (Nat.card { x // x in rootsOfUnity n L })).val :=
  modularCyclotomicCharacter.toFun_spec' g ht

/--
lemma `modularCyclotomicCharacter'.unique'` / 引理 `modularCyclotomicCharacter'.unique'`

English:
lemma modularCyclotomicCharacter'.unique'
  statement: (g : L ≃+* L)
  proof: modularCyclotomicCharacter.toFun_unique' _ _ _ hc

中文:
引理 modularCyclotomicCharacter'.unique'
  结论: (g : L ≃+* L)
  证明: modularCyclotomicCharacter.toFun_unique' _ _ _ hc
-/
lemma modularCyclotomicCharacter'.unique' (g : L ≃+* L)
    {c : ZMod (Nat.card { x // x in rootsOfUnity n L })}
    (hc : forall t in rootsOfUnity n L, g t = t ^ c.val) :
    c = modularCyclotomicCharacter' L n g :=
  modularCyclotomicCharacter.toFun_unique' _ _ _ hc

/--
Definition of `modularCyclotomicCharacter` / `modularCyclotomicCharacter` 的定义

English:
definition modularCyclotomicCharacter
  signature: {n : Nat} [NeZero n]
  body: (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (modularCyclotomicCharacter' L n)

中文:
定义 modularCyclotomicCharacter
  签名: {n : 自然数} [NeZero n]
  定义体: (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (modularCyclotomicCharacter' L n)

Depends on / 依赖: Units.mapEquiv, ZMod.ringEquivCongr, mapEquiv, modularCyclotomicCharacter, ringEquivCongr, toMonoidHom, toMonoidHom.comp, toMulEquiv
-/
noncomputable def modularCyclotomicCharacter {n : Nat} [NeZero n]
    (hn : Nat.card { x // x in rootsOfUnity n L } = n) :
    (L ≃+* L) ->* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (modularCyclotomicCharacter' L n)

namespace modularCyclotomicCharacter

variable {n : Nat} [NeZero n] (hn : Nat.card { x // x in rootsOfUnity n L } = n)

/--
lemma `spec` / 引理 `spec`

English:
lemma spec
  given: (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L)
  proof: by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

中文:
引理 spec
  条件: (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L)
  证明: by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

Depends on / 依赖: ZMod.ringEquivCongr_val, ringEquivCongr_val, toFun_spec
-/
lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L) :
    g t = t ^ ((modularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: (g : L ≃+* L) {c : ZMod n} (hc : forall t in rootsOfUnity n L, g t = t ^ c.val)
  proof: by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht => by rw [hc t ht]; rw [ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

中文:
引理 unique
  条件: (g : L ≃+* L) {c : ZMod n} (hc : 对任意 t in rootsOfUnity n L, g t = t ^ c.val)
  证明: by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht => by rw [hc t ht]; rw [ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

Depends on / 依赖: RingEquiv, RingEquiv.apply_symm_apply, ZMod.ringEquivCongr, ZMod.ringEquivCongr_symm, ZMod.ringEquivCongr_val, apply_symm_apply, hn.symm, ringEquivCongr, ringEquivCongr_symm, ringEquivCongr_val, toFun_unique
-/
lemma unique (g : L ≃+* L) {c : ZMod n} (hc : forall t in rootsOfUnity n L, g t = t ^ c.val) :
    c = modularCyclotomicCharacter L hn g := by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht => by rw [hc t ht]; rw [ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

end modularCyclotomicCharacter

variable {L}

/--
lemma `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter` / 引理 `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter`

English:
lemma IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
  statement: (n : Nat) [NeZero n]
  proof: by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa only [autToPow_spec R hμ g, modularCyclotomicCharacter, RingEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, modularCyclotomicCharacter', MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_a

中文:
引理 IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
  结论: (n : 自然数) [NeZero n]
  证明: by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa only [autToPow_spec R hμ g, modularCyclotomicCharacter, RingEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, modularCyclotomicCharacter', MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_a

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ringEquiv, Function, Function.comp_apply, MonoidHom, MonoidHom.coe_coe, MonoidHom.coe_comp, MonoidHom.coe_mk, MonoidHom.coe_toHomUnits, MulEquiv, MulEquiv.toMonoidHom_eq_coe, OneHom, OneHom.coe_mk, RingEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.toMulEquiv_eq_coe, Units.coe_mapEquiv, ZMod.ringEquivCongr_val, ZMod.val_injective, ZMod.val_lt
-/
lemma IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter (n : Nat) [NeZero n]
    (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g : Gal(L/R)) :
    hμ.autToPow R g = modularCyclotomicCharacter L hμ.card_rootsOfUnity g := by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa only [autToPow_spec R hμ g, modularCyclotomicCharacter, RingEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, modularCyclotomicCharacter', MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply, Units.coe_mapEquiv, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk,
    OneHom.coe_mk, RingEquiv.coe_toMulEquiv, ZMod.ringEquivCongr_val, AlgEquiv.coe_ringEquiv]
    using modularCyclotomicCharacter.toFun_spec'' g hμ

/-

## The p-adic theory

-/

open modularCyclotomicCharacter in
open scoped Classical in
/--
Definition of `cyclotomicCharacter.toFun` / `cyclotomicCharacter.toFun` 的定义

English:
definition cyclotomicCharacter.toFun
  signature: (p : Nat) [Fact p.Prime] (g : L ≃+* L)
  body: if H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i) then
    haveI _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (aux g <| p ^ ·) _ fun i => pow_dvd_aux_pow_sub_aux_pow g p i.le_succ)

中文:
定义 cyclotomicCharacter.toFun
  签名: (p : 自然数) [Fact p.Prime] (g : L ≃+* L)
  定义体: if H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i) then
    haveI _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (aux g <| p ^ ·) _ fun i => pow_dvd_aux_pow_sub_aux_pow g p i.le_succ)

Depends on / 依赖: HasEnoughRootsOfUnity, IsPrimitiveRoot, PadicInt, PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub, PadicInt.ofIntSeq, i.le_succ, isCauSeq_padicNorm_of_pow_dvd_sub, isCyclic, le_succ, ofIntSeq, pow_dvd_aux_pow_sub_aux_pow, rootsOfUnity, rootsOfUnity.isCyclic
-/
noncomputable def cyclotomicCharacter.toFun (p : Nat) [Fact p.Prime] (g : L ≃+* L) : Int_[p] :=
  if H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i) then
    haveI _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (aux g <| p ^ ·) _ fun i => pow_dvd_aux_pow_sub_aux_pow g p i.le_succ)
  else 1

namespace cyclotomicCharacter

local notation "χ" => cyclotomicCharacter.toFun

variable (p : Nat) [Fact p.Prime] (g : L ≃+* L) [forall i, HasEnoughRootsOfUnity L (p ^ i)]

open modularCyclotomicCharacter in
/--
theorem `toFun_apply` / 定理 `toFun_apply`

English:
theorem toFun_apply
  proof: dif_pos fun _ => HasEnoughRootsOfUnity.exists_primitiveRoot _ _

中文:
定理 toFun_apply
  证明: dif_pos fun _ => HasEnoughRootsOfUnity.exists_primitiveRoot _ _

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.exists_primitiveRoot, dif_pos, exists_primitiveRoot
-/
theorem toFun_apply :
    cyclotomicCharacter.toFun p g =
      PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (aux g <| p ^ ·) _ fun i => pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) :=
  dif_pos fun _ => HasEnoughRootsOfUnity.exists_primitiveRoot _ _

open modularCyclotomicCharacter in
/--
theorem `toZModPow_toFun` / 定理 `toZModPow_toFun`

English:
theorem toZModPow_toFun
  given: (n : Nat)
  proof: by
  rw [toFun_apply]
  refine (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (aux g <| p ^ ·) _ (fun i =>
    pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) n).trans ?_
  simp [modularCyclotomicCharacter, modularCyclotomicCharacter', modularCyclotomicCharacter.toFun]

中文:
定理 toZModPow_toFun
  条件: (n : 自然数)
  证明: by
  rw [toFun_apply]
  refine (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (aux g <| p ^ ·) _ (fun i =>
    pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) n).trans ?_
  simp [modularCyclotomicCharacter, modularCyclotomicCharacter', modularCyclotomicCharacter.toFun]

Depends on / 依赖: PadicInt, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, i.le_succ, le_succ, modularCyclotomicCharacter, modularCyclotomicCharacter.toFun, pow_dvd_aux_pow_sub_aux_pow, toFun_apply, toZModPow_ofIntSeq_of_pow_dvd_sub
-/
theorem toZModPow_toFun (n : Nat) :
    (χ p g).toZModPow n =
      (modularCyclotomicCharacter _
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g).val := by
  rw [toFun_apply]
  refine (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (aux g <| p ^ ·) _ (fun i =>
    pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) n).trans ?_
  simp [modularCyclotomicCharacter, modularCyclotomicCharacter', modularCyclotomicCharacter.toFun]

/--
theorem `toFun_spec` / 定理 `toFun_spec`

English:
theorem toFun_spec
  given: (g : L ≃+* L) {n : Nat} (t : rootsOfUnity (p ^ n) L)
  proof: by
  rw [toZModPow_toFun]; rw [← modularCyclotomicCharacter.spec (ht := t.2)]

中文:
定理 toFun_spec
  条件: (g : L ≃+* L) {n : 自然数} (t : rootsOfUnity (p ^ n) L)
  证明: by
  rw [toZModPow_toFun]; rw [← modularCyclotomicCharacter.spec (ht := t.2)]

Depends on / 依赖: modularCyclotomicCharacter, modularCyclotomicCharacter.spec, toZModPow_toFun
-/
theorem toFun_spec (g : L ≃+* L) {n : Nat} (t : rootsOfUnity (p ^ n) L) :
    g (t : Lˣ) = t.1 ^ ((χ p g).toZModPow n).val := by
  rw [toZModPow_toFun]; rw [← modularCyclotomicCharacter.spec (ht := t.2)]

end cyclotomicCharacter

variable (L) in
/--
Definition of `cyclotomicCharacter` / `cyclotomicCharacter` 的定义

English:
definition cyclotomicCharacter
  signature: (p : Nat) [Fact p.Prime]
  body: .toHomUnits
  { toFun g := cyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  

中文:
定义 cyclotomicCharacter
  签名: (p : 自然数) [Fact p.Prime]
  定义体: .toHomUnits
  { toFun g := cyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  

Depends on / 依赖: toHomUnits
-/
noncomputable def cyclotomicCharacter (p : Nat) [Fact p.Prime] :
    (L ≃+* L) ->* Int_[p]ˣ := .toHomUnits
  { toFun g := cyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n => ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dif_neg H]
    map_mul' f g := by
      by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n => ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dif_neg H] }

/--
theorem `cyclotomicCharacter.spec` / 定理 `cyclotomicCharacter.spec`

English:
theorem cyclotomicCharacter.spec
  statement: (p : Nat) [Fact p.Prime] {n : Nat}
  proof: toFun_spec p g (rootsOfUnity.mkOfPowEq _ ht)

中文:
定理 cyclotomicCharacter.spec
  结论: (p : 自然数) [Fact p.Prime] {n : 自然数}
  证明: toFun_spec p g (rootsOfUnity.mkOfPowEq _ ht)

Depends on / 依赖: mkOfPowEq, rootsOfUnity, rootsOfUnity.mkOfPowEq, toFun_spec
-/
theorem cyclotomicCharacter.spec (p : Nat) [Fact p.Prime] {n : Nat}
    [forall i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) (t : L) (ht : t ^ p ^ n = 1) :
    g t = t ^ ((cyclotomicCharacter L p g).val.toZModPow n).val :=
  toFun_spec p g (rootsOfUnity.mkOfPowEq _ ht)

/--
theorem `cyclotomicCharacter.toZModPow` / 定理 `cyclotomicCharacter.toZModPow`

English:
theorem cyclotomicCharacter.toZModPow
  statement: (p : Nat) [Fact p.Prime] {n : Nat}
  proof: toZModPow_toFun _ _ _

中文:
定理 cyclotomicCharacter.toZModPow
  结论: (p : 自然数) [Fact p.Prime] {n : 自然数}
  证明: toZModPow_toFun _ _ _

Depends on / 依赖: toZModPow_toFun
-/
theorem cyclotomicCharacter.toZModPow (p : Nat) [Fact p.Prime] {n : Nat}
    [forall i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) :
    (cyclotomicCharacter L p g).val.toZModPow n =
      (modularCyclotomicCharacter _
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g).val :=
  toZModPow_toFun _ _ _

open IntermediateField in
/--
lemma `cyclotomicCharacter.continuous` / 引理 `cyclotomicCharacter.continuous`

English:
lemma cyclotomicCharacter.continuous
  statement: (p : Nat) [Fact p.Prime]
  proof: by
  by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i); swap
  · simp only [cyclotomicCharacter, cyclotomicCharacter.toFun, dif_neg H, MonoidHom.coe_comp]
    exact continuous_const (y := 1)
  have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
  cho

中文:
引理 cyclotomicCharacter.continuous
  结论: (p : 自然数) [Fact p.Prime]
  证明: by
  by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i); swap
  · simp only [cyclotomicCharacter, cyclotomicCharacter.toFun, dif_neg H, MonoidHom.coe_comp]
    exact continuous_const (y := 1)
  have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
  cho

Depends on / 依赖: Continuous, Continuous.of_coeHom_comp, ContinuousAt, HasEnoughRootsOfUnity, Int_, IsPrimitiveRoot, Metric, Metric.nhds_basis_ball, MonoidHom, MonoidHom.coe_comp, coe_comp, continuous_const, continuous_of_continuousAt_one, cyclotomicCharacter, cyclotomicCharacter.toFun, dif_neg, galGroupBasis, isCyclic, map_one, nhds_basis_ball
-/
lemma cyclotomicCharacter.continuous (p : Nat) [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Continuous ((cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)) := by
  by_cases H : forall (i : Nat), exists ζ : L, IsPrimitiveRoot ζ (p ^ i); swap
  · simp only [cyclotomicCharacter, cyclotomicCharacter.toFun, dif_neg H, MonoidHom.coe_comp]
    exact continuous_const (y := 1)
  have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
  choose ζ hζ using H
  refine Continuous.of_coeHom_comp ?_
  apply continuous_of_continuousAt_one
  rw [ContinuousAt]; rw [map_one]; rw [(galGroupBasis K L).nhds_one_hasBasis.tendsto_iff
    (Metric.nhds_basis_ball (α := Int_[p]) (x := 1))]
  intro ε hε
  obtain ⟨k, hk', hk⟩ : exists k : Nat, k != 0 ∧ p ^ (-k : Int) < ε := by
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    exact ⟨k + 1, by simp, lt_of_le_of_lt (by gcongr <;> simp [‹Fact p.Prime›.1.one_le]) hk⟩
  refine ⟨_, ⟨_, ⟨(K⟮ζ k⟯), adjoin.finiteDimensional ?_, rfl⟩, rfl⟩, ?_⟩
  · exact ((hζ k).isIntegral (Nat.pos_of_neZero _)).tower_top
  · intro σ hσ
    refine lt_of_le_of_lt ?_ hk
    dsimp
    rw [dist_eq_norm]; rw [PadicInt.norm_le_pow_iff_mem_span_pow]; rw [← PadicInt.ker_toZModPow]; rw [RingHom.mem_ker]; rw [map_sub]; rw [map_one]; rw [cyclotomicCharacter.toZModPow]; rw [sub_eq_zero]; rw [eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := ((hζ k).isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'']; rw [pow_one]
    · exact hσ ⟨ζ k ^ i, pow_mem (mem_adjoin_simple_self K (ζ k)) _⟩
    · exact (one_lt_pow₀ ‹Fact p.Prime›.1.one_lt hk').ne'
