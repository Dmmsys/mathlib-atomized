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

variable (n : ℕ) [NeZero n]

/-
**rootsOfUnity.integer_power_of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) : exists m : Int, fo
rall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ)
参数：g : L ≃+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MonoidHom.map_cyclic`：MonoidHom.map_cyclic [h : IsCyclic G] (σ : G ->* G
) : exists m : Int, forall g : G, σ g = g ^ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetCoe.ext_iff`：SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a
 = b
-/
theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
  exact ⟨m, fun t ↦ Units.ext_iff.1 <| SetCoe.ext_iff.2 <| hm t⟩
/-
**rootsOfUnity.integer_power_of_ringEquiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) : exists m : Int, f
orall t in rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ)
参数：g : L ≃+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `rootsOfUnity.integer_power_of_ringEquiv`：rootsOfUnity.integer_power_of_r
ingEquiv (g : L ≃+* L) : exists m : Int, forall t : rootsOfUnity n L, g (t : Lˣ)
 = (t ^ m : Lˣ)
-/
theorem rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t ∈ rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

/-- `modularCyclotomicCharacter_aux g n` is a non-canonical auxiliary integer `j`,
  only well-defined modulo the number of `n`-th roots of unity in `L`, such that `g(ζ)=ζ^j`
  for all `n`-th roots of unity `ζ` in `L`. -/
/-
**modularCyclotomicCharacter.aux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modularCyclotomicCharacter.aux (g : L ≃+* L) (n : Nat) [NeZero n] : Int
参数：g : L ≃+* L；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `rootsOfUnity.integer_power_of_ringEquiv`：rootsOfUnity.integer_power_of_r
ingEquiv (g : L ≃+* L) : exists m : Int, forall t : rootsOfUnity n L, g (t : Lˣ)
 = (t ^ m : Lˣ)

--- 原说明 ---
`modularCyclotomicCharacter_aux g n` is a non-canonical auxiliary integer `j`,
  only well-defined modulo the number of `n`-th roots of unity in `L`, such that
 `g(ζ)=ζ^j`
  for all `n`-th roots of unity `ζ` in `L`.
-/
noncomputable def modularCyclotomicCharacter.aux (g : L ≃+* L) (n : ℕ) [NeZero n] : ℤ :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose

-- the only thing we know about `modularCyclotomicCharacter_aux g n`
/-
**modularCyclotomicCharacter.aux_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modularCyclotomicCharacter.aux_spec (g : L ≃+* L) (n : Nat) [NeZero n] : f
orall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (modularCyclotomicCharacter.aux g 
n) : Lˣ)
参数：g : L ≃+* L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `rootsOfUnity.integer_power_of_ringEquiv`：rootsOfUnity.integer_power_of_r
ingEquiv (g : L ≃+* L) : exists m : Int, forall t : rootsOfUnity n L, g (t : Lˣ)
 = (t ^ m : Lˣ)
-/
theorem modularCyclotomicCharacter.aux_spec (g : L ≃+* L) (n : ℕ) [NeZero n] :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (modularCyclotomicCharacter.aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec
/-
**modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow (g : L ≃+* L) (p : 
Nat) [Fact p.Prime] [forall i, HasEnoughRootsOfUnity L (p ^ i)] {i k : Nat} (hi 
: k <= i) : (p : Int) ^ k ∣ aux g (p ^ i) - aux g (p ^ k)
参数：g : L ≃+* L；p : Nat；p ^ i；hi : k <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `HasEnoughRootsOfUnity.exists_primitiveRoot`：exists_primitiveRoot (M : Ty
pe*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] : exists ζ : M, IsPrim
itiveRoot ζ n
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `Nat.pow_add'`：∀ (a m n : ℕ), a ^ (m + n) = a ^ n * a ^ m
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `IsPrimitiveRoot.mem_rootsOfUnity`：∀ {M : Type u_1} [inst : CommMonoid M]
 {ζ : Mˣ} {n : ℕ}, IsPrimitiveRoot ζ n → ζ ∈ rootsOfUnity n M
· 使用引理 `IsPrimitiveRoot.isUnit_unit`：isUnit_unit {ζ : M} {n} (hn) (hζ : IsPrimit
iveRoot ζ n) : IsPrimitiveRoot (hζ.isUnit hn).unit n
· 使用定理 `modularCyclotomicCharacter.aux_spec`：modularCyclotomicCharacter.aux_spec
 (g : L ≃+* L) (n : Nat) [NeZero n] : forall t : rootsOfUnity n L, g (t : Lˣ) = 
(t ^ (modularCyclotomicCh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
（共 44 条，此处仅展示前 30 条）
-/
theorem modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow
    (g : L ≃+* L) (p : ℕ) [Fact p.Prime] [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    {i k : ℕ} (hi : k ≤ i) : (p : ℤ) ^ k ∣ aux g (p ^ i) - aux g (p ^ k) := by
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
  rw [H₁, ← Units.val_pow_eq_pow_val, ← Units.ext_iff, h_unit, ← div_eq_one] at H₂
  simp only [← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_sub] at H₂
  rw [(hζ.isUnit_unit NeZero.out).zpow_eq_one_iff_dvd, mul_comm, ← mul_sub] at H₂
  conv_lhs at H₂ => rw [Nat.pow_add', Nat.cast_mul]
  rwa [mul_dvd_mul_iff_left (by simp [NeZero.ne p]), Nat.cast_pow] at H₂

/-- If `g` is a ring automorphism of `L`, and `n : ℕ+`, then
  `modularCyclotomicCharacter.toFun n g` is the `j : ZMod d` such that `g(ζ)=ζ^j` for all
  `n`-th roots of unity. Here `d` is the number of `n`th roots of unity in `L`. -/
/-
**modularCyclotomicCharacter.toFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modularCyclotomicCharacter.toFun (n : Nat) [NeZero n] (g : L ≃+* L) : ZMod
 (Nat.card (rootsOfUnity n L))
参数：n : Nat；g : L ≃+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a ring automorphism of `L`, and `n : ℕ+`, then
  `modularCyclotomicCharacter.toFun n g` is the `j : ZMod d` such that `g(ζ)=ζ^j
` for all
  `n`-th roots of unity. Here `d` is the number of `n`th roots of unity in `L`.
-/
noncomputable def modularCyclotomicCharacter.toFun (n : ℕ) [NeZero n] (g : L ≃+* L) :
    ZMod (Nat.card (rootsOfUnity n L)) :=
  modularCyclotomicCharacter.aux g n

namespace modularCyclotomicCharacter

local notation "χ₀" => modularCyclotomicCharacter.toFun

/-- The formula which characterises the output of `modularCyclotomicCharacter g n`. -/
/-
**modularCyclotomicCharacter.toFun_spec** 是 Mathlib 中的一个定理，位于命名空间 `modularCyclot
omicCharacter`。
形式化陈述：toFun_spec (g : L ≃+* L) {n : Nat} [NeZero n] (t : rootsOfUnity n L) : g (
t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ)
参数：g : L ≃+* L；t : rootsOfUnity n L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modularCyclotomicCharacter.aux_spec`：modularCyclotomicCharacter.aux_spec
 (g : L ≃+* L) (n : Nat) [NeZero n] : forall t : rootsOfUnity n L, g (t : Lˣ) = 
(t ^ (modularCyclotomicCh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `modularCyclotomicCharacter.toFun.eq_1`：∀ {L : Type u} [inst : CommRing L
] [inst_1 : IsDomain L] (n : ℕ) [inst_2 : NeZero n] (g : L ≃+* L),   modularCycl
otomicCharacter.toFun n g =…
· 使用定理 `ZMod.val_intCast`：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMo
d n).val = a % n
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `Subgroup.coe_zpow`：coe_zpow (x : H) (n : Int) : ((x ^ n : H) : G) = (x :
 G) ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetCoe.ext_iff`：SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a
 = b
· 使用定理 `zpow_eq_zpow_emod`：zpow_eq_zpow_emod {x : G} (m : Int) {n : Int} (h : x 
^ n = 1) : x ^ m = x ^ (m % n)
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1

--- 原说明 ---
The formula which characterises the output of `modularCyclotomicCharacter g n`.
-/
theorem toFun_spec (g : L ≃+* L) {n : ℕ} [NeZero n] (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ) := by
  rw [modularCyclotomicCharacter.aux_spec g n t, ← zpow_natCast, modularCyclotomicCharacter.toFun,
    ZMod.val_intCast, ← Subgroup.coe_zpow]
  exact Units.ext_iff.1 <| SetCoe.ext_iff.2 <|
    zpow_eq_zpow_emod _ pow_card_eq_one' (G := rootsOfUnity n L)
/-
**modularCyclotomicCharacter.toFun_spec'** 是 Mathlib 中的一个定理，位于命名空间 `modularCyclo
tomicCharacter`。
形式化陈述：toFun_spec' (g : L ≃+* L) {n : Nat} [NeZero n] {t : Lˣ} (ht : t in rootsOf
Unity n L) : g t = t ^ (χ₀ n g).val
参数：g : L ≃+* L；ht : t in rootsOfUnity n L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `modularCyclotomicCharacter.toFun_spec`：toFun_spec (g : L ≃+* L) {n : Nat
} [NeZero n] (t : rootsOfUnity n L) : g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ)
-/
theorem toFun_spec' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec g ⟨t, ht⟩
/-
**modularCyclotomicCharacter.toFun_spec''** 是 Mathlib 中的一个定理，位于命名空间 `modularCycl
otomicCharacter`。
形式化陈述：toFun_spec'' (g : L ≃+* L) {n : Nat} [NeZero n] {t : L} (ht : IsPrimitiveR
oot t n) : g t = t ^ (χ₀ n g).val
参数：g : L ≃+* L；ht : IsPrimitiveRoot t n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `modularCyclotomicCharacter.toFun_spec'`：toFun_spec' (g : L ≃+* L) {n : N
at} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L) : g t = t ^ (χ₀ n g).val
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem toFun_spec'' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

/-- If g(t)=t^c for all roots of unity, then c=χ(g). -/
/-
**modularCyclotomicCharacter.toFun_unique** 是 Mathlib 中的一个定理，位于命名空间 `modularCycl
otomicCharacter`。
形式化陈述：toFun_unique (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L))) (hc : 
forall t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g
参数：g : L ≃+* L；c : ZMod (Nat.card (rootsOfUnity n L))；hc : forall t : rootsOfUni
ty n L, g (t : Lˣ) = (t ^ c.val : Lˣ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCyclic.ext`：IsCyclic.ext [Finite G] [IsCyclic G] {d : Nat} {a b : ZMod
 d} (hGcard : Nat.card G = d) (h : forall t : G, t ^ a.val = t ^ b.val) : a = b
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `modularCyclotomicCharacter.toFun_spec`：toFun_spec (g : L ≃+* L) {n : Nat
} [NeZero n] (t : rootsOfUnity n L) : g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ)
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If g(t)=t^c for all roots of unity, then c=χ(g).
-/
theorem toFun_unique (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
    (hc : ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext rfl (fun ζ ↦ ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ, hc]
/-
**modularCyclotomicCharacter.toFun_unique'** 是 Mathlib 中的一个定理，位于命名空间 `modularCyc
lotomicCharacter`。
形式化陈述：toFun_unique' (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L))) (hc :
 forall t in rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g
参数：g : L ≃+* L；c : ZMod (Nat.card (rootsOfUnity n L))；hc : forall t in rootsOfUn
ity n L, g t = t ^ c.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `modularCyclotomicCharacter.toFun_unique`：toFun_unique (g : L ≃+* L) (c :
 ZMod (Nat.card (rootsOfUnity n L))) (hc : forall t : rootsOfUnity n L, g (t : L
ˣ) = (t ^ c.val : Lˣ)) : c = …
-/
theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Nat.card (rootsOfUnity n L)))
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ ↦ hc _ ht)
/-
**modularCyclotomicCharacter.id** 是 Mathlib 中的一个引理，位于命名空间 `modularCyclotomicChar
acter`。
形式化陈述：id : χ₀ n (RingEquiv.refl L) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `modularCyclotomicCharacter.toFun_unique`：toFun_unique (g : L ≃+* L) (c :
 ZMod (Nat.card (rootsOfUnity n L))) (hc : forall t : rootsOfUnity n L, g (t : L
ˣ) = (t ^ c.val : Lˣ)) : c = …
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton [Finit
e α] : Nat.card α <= 1 ↔ Subsingleton α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t ↦ ?_).symm
  have : 1 ≤ Nat.card { x // x ∈ rootsOfUnity n L } := Nat.card_pos
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Finite.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp
/-
**modularCyclotomicCharacter.comp** 是 Mathlib 中的一个引理，位于命名空间 `modularCyclotomicCh
aracter`。
形式化陈述：comp (g h : L ≃+* L) : χ₀ n (g * h) = χ₀ n g * χ₀ n h
参数：g h : L ≃+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `modularCyclotomicCharacter.toFun_unique`：toFun_unique (g : L ≃+* L) (c :
 ZMod (Nat.card (rootsOfUnity n L))) (hc : forall t : rootsOfUnity n L, g (t : L
ˣ) = (t ^ c.val : Lˣ)) : c = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modularCyclotomicCharacter.toFun_spec`：toFun_spec (g : L ≃+* L) {n : Nat
} [NeZero n] (t : rootsOfUnity n L) : g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ)
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `ZMod.cast_mul`：cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod
 n) : R) = cast a * cast b
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
    χ₀ n g * χ₀ n h := by
  refine (toFun_unique n (g * h) _ <| fun ζ ↦ ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec, ← Subgroup.coe_pow, toFun_spec, mul_comm, Subgroup.coe_pow, ← pow_mul,
    ← Subgroup.coe_pow]
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
/-
**modularCyclotomicCharacter'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modularCyclotomicCharacter' (n : Nat) [NeZero n] : (L ≃+* L) ->* (ZMod (Na
t.card { x // x in rootsOfUnity n L }))ˣ
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `modularCyclotomicCharacter.id`：id : χ₀ n (RingEquiv.refl L) = 1
· 使用引理 `modularCyclotomicCharacter.comp`：comp (g h : L ≃+* L) : χ₀ n (g * h) = χ
₀ n g * χ₀ n h
-/
def modularCyclotomicCharacter' (n : ℕ) [NeZero n] :
    (L ≃+* L) →* (ZMod (Nat.card { x // x ∈ rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := modularCyclotomicCharacter.toFun n
    map_one' := modularCyclotomicCharacter.id n
    map_mul' := modularCyclotomicCharacter.comp n }
/-
**modularCyclotomicCharacter'.spec'** 是 Mathlib 中的一个定理，位于命名空间 `modularCyclotomic
Character'`。
形式化陈述：∀ (L : Type u) [inst : CommRing L] [inst_1 : IsDomain L] (n : ℕ) [inst_2 :
 NeZero n] (g : L ≃+* L) {t : Lˣ},   t ∈ rootsOfUnity n L → g ↑t = ↑t ^ (↑((modu
larCyclotomicCharacter' L n) g)).val
参数：L : Type u；n : ℕ；g : L ≃+* L；↑((modularCyclotomicCharacter' L n) g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `modularCyclotomicCharacter.toFun_spec'`：toFun_spec' (g : L ≃+* L) {n : N
at} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L) : g t = t ^ (χ₀ n g).val
-/
lemma modularCyclotomicCharacter'.spec' (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((modularCyclotomicCharacter' L n g) : ZMod
      (Nat.card { x // x ∈ rootsOfUnity n L })).val :=
  modularCyclotomicCharacter.toFun_spec' g ht
/-
**modularCyclotomicCharacter'.unique'** 是 Mathlib 中的一个定理，位于命名空间 `modularCyclotom
icCharacter'`。
形式化陈述：∀ (L : Type u) [inst : CommRing L] [inst_1 : IsDomain L] (n : ℕ) [inst_2 :
 NeZero n] (g : L ≃+* L)   {c : ZMod (Nat.card ↥(rootsOfUnity n L))},   (∀ t ∈ r
ootsOfUnity n L, g ↑t = ↑t ^ c.val) → c = ↑((modularCyclotomicCharacter' L n) g)
参数：L : Type u；n : ℕ；g : L ≃+* L；Nat.card ↥(rootsOfUnity n L)；∀ t ∈ rootsOfUnity 
n L, g ↑t = ↑t ^ c.val；(modularCyclotomicCharacter' L n) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `modularCyclotomicCharacter.toFun_unique'`：toFun_unique' (g : L ≃+* L) (c
 : ZMod (Nat.card (rootsOfUnity n L))) (hc : forall t in rootsOfUnity n L, g t =
 t ^ c.val) : c = χ₀ n g
-/
lemma modularCyclotomicCharacter'.unique' (g : L ≃+* L)
    {c : ZMod (Nat.card { x // x ∈ rootsOfUnity n L })}
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = modularCyclotomicCharacter' L n g :=
  modularCyclotomicCharacter.toFun_unique' _ _ _ hc

/-- Given a positive integer `n` and a field `L` containing `n` `n`th roots
of unity, `modularCyclotomicCharacter n` is a multiplicative homomorphism from the
automorphisms of `L` to `(ℤ/nℤ)ˣ`. It is uniquely characterised by the property that
`g(ζ)=ζ^(modularCyclotomicCharacter n g)` for `g` an automorphism of `L` and `ζ` any `n`th root
of unity. -/
/-
**modularCyclotomicCharacter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modularCyclotomicCharacter {n : Nat} [NeZero n] (hn : Nat.card { x // x in
 rootsOfUnity n L } = n) : (L ≃+* L) ->* (ZMod n)ˣ
参数：hn : Nat.card { x // x in rootsOfUnity n L } = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a positive integer `n` and a field `L` containing `n` `n`th roots
of unity, `modularCyclotomicCharacter n` is a multiplicative homomorphism from t
he
automorphisms of `L` to `(ℤ/nℤ)ˣ`. It is uniquely characterised by the property 
that
`g(ζ)=ζ^(modularCyclotomicCharacter n g)` for `g` an automorphism of `L` and `ζ`
 any `n`th root
of unity.
-/
noncomputable def modularCyclotomicCharacter {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n L } = n) :
    (L ≃+* L) →* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (modularCyclotomicCharacter' L n)

namespace modularCyclotomicCharacter

variable {n : ℕ} [NeZero n] (hn : Nat.card { x // x ∈ rootsOfUnity n L } = n)

/-
**modularCyclotomicCharacter.spec** 是 Mathlib 中的一个引理，位于命名空间 `modularCyclotomicCh
aracter`。
形式化陈述：spec (g : L ≃+* L) {t : Lˣ} (ht : t in rootsOfUnity n L) : g t = t ^ ((mod
ularCyclotomicCharacter L hn g) : ZMod n).val
参数：g : L ≃+* L；ht : t in rootsOfUnity n L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modularCyclotomicCharacter.toFun_spec'`：toFun_spec' (g : L ≃+* L) {n : N
at} [NeZero n] {t : Lˣ} (ht : t in rootsOfUnity n L) : g t = t ^ (χ₀ n g).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZMod.ringEquivCongr_val`：ringEquivCongr_val {a b : Nat} (h : a = b) (x :
 ZMod a) : ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x
-/
lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((modularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm
/-
**modularCyclotomicCharacter.unique** 是 Mathlib 中的一个引理，位于命名空间 `modularCyclotomic
Character`。
形式化陈述：unique (g : L ≃+* L) {c : ZMod n} (hc : forall t in rootsOfUnity n L, g t 
= t ^ c.val) : c = modularCyclotomicCharacter L hn g
参数：g : L ≃+* L；hc : forall t in rootsOfUnity n L, g t = t ^ c.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modularCyclotomicCharacter.toFun_unique'`：toFun_unique' (g : L ≃+* L) (c
 : ZMod (Nat.card (rootsOfUnity n L))) (hc : forall t in rootsOfUnity n L, g t =
 t ^ c.val) : c = χ₀ n g
· 使用引理 `ZMod.ringEquivCongr_val`：ringEquivCongr_val {a b : Nat} (h : a = b) (x :
 ZMod a) : ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x
· 使用引理 `ZMod.ringEquivCongr_symm`：ringEquivCongr_symm {a b : Nat} (hab : a = b) 
: (ringEquivCongr hab).symm = ringEquivCongr hab.symm
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
lemma unique (g : L ≃+* L) {c : ZMod n} (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = modularCyclotomicCharacter L hn g := by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht ↦ by rw [hc t ht, ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

end modularCyclotomicCharacter

variable {L}

/-- The relationship between `IsPrimitiveRoot.autToPow` and
`modularCyclotomicCharacter`. Note that `IsPrimitiveRoot.autToPow`
needs an explicit root of unity, and also an auxiliary "base ring" `R`. -/
/-
**IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter (n : Nat) [NeZero n
] (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g :
 Gal(L/R)) : hμ.autToPow R g = modularCyclotomicCharacter L hμ.card_rootsOfUnity
 g
参数：n : Nat；R : Type*；hμ : IsPrimitiveRoot μ n；g : Gal(L/R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `IsPrimitiveRoot.card_rootsOfUnity`：card_rootsOfUnity {ζ : R} {n : Nat} [
NeZero n] (h : IsPrimitiveRoot ζ n) : Nat.card (rootsOfUnity n R) = n
· 使用定理 `ZMod.val_injective`：val_injective (n : Nat) [NeZero n] : Function.Inject
ive (val : ZMod n -> Nat)
· 使用定理 `IsPrimitiveRoot.pow_inj`：pow_inj (h : IsPrimitiveRoot ζ k) ⦃i j : Nat⦄ (
hi : i < k) (hj : j < k) (H : ζ ^ i = ζ ^ j) : i = j
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.autToPow_spec`：autToPow_spec [NeZero n] (f : S ≃ₐ[R] S) 
: μ ^ (hμ.autToPow R f : ZMod n).val = f μ
· 使用引理 `ZMod.ringEquivCongr_val`：ringEquivCongr_val {a b : Nat} (h : a = b) (x :
 ZMod a) : ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x
· 使用定理 `modularCyclotomicCharacter.toFun_spec''`：toFun_spec'' (g : L ≃+* L) {n :
 Nat} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n) : g t = t ^ (χ₀ n g).val

--- 原说明 ---
The relationship between `IsPrimitiveRoot.autToPow` and
`modularCyclotomicCharacter`. Note that `IsPrimitiveRoot.autToPow`
needs an explicit root of unity, and also an auxiliary "base ring" `R`.
-/
lemma IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter (n : ℕ) [NeZero n]
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
/-- The underlying function of the cyclotomic character. See `cyclotomicCharacter`. -/
/-
**cyclotomicCharacter.toFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cyclotomicCharacter.toFun (p : Nat) [Fact p.Prime] (g : L ≃+* L) : Int_[p]
参数：p : Nat；g : L ≃+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function of the cyclotomic character. See `cyclotomicCharacter`.
-/
noncomputable def cyclotomicCharacter.toFun (p : ℕ) [Fact p.Prime] (g : L ≃+* L) : ℤ_[p] :=
  if H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i) then
    haveI _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (aux g <| p ^ ·) _ fun i ↦ pow_dvd_aux_pow_sub_aux_pow g p i.le_succ)
  else 1

namespace cyclotomicCharacter

local notation "χ" => cyclotomicCharacter.toFun

variable (p : ℕ) [Fact p.Prime] (g : L ≃+* L) [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

open modularCyclotomicCharacter in
/-
**cyclotomicCharacter.toFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `cyclotomicCharacter
`。
形式化陈述：toFun_apply : cyclotomicCharacter.toFun p g = PadicInt.ofIntSeq _ (PadicIn
t.isCauSeq_padicNorm_of_pow_dvd_sub (aux g <| p ^ ·) _ fun i => pow_dvd_aux_pow_
sub_aux_pow g p i.le_succ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `HasEnoughRootsOfUnity.exists_primitiveRoot`：exists_primitiveRoot (M : Ty
pe*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] : exists ζ : M, IsPrim
itiveRoot ζ n
-/
theorem toFun_apply :
    cyclotomicCharacter.toFun p g =
      PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (aux g <| p ^ ·) _ fun i ↦ pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) :=
  dif_pos fun _ ↦ HasEnoughRootsOfUnity.exists_primitiveRoot _ _

open modularCyclotomicCharacter in
/-
**cyclotomicCharacter.toZModPow_toFun** 是 Mathlib 中的一个定理，位于命名空间 `cyclotomicChara
cter`。
形式化陈述：toZModPow_toFun (n : Nat) : (χ p g).toZModPow n = (modularCyclotomicCharac
ter _ (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g).val
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `HasEnoughRootsOfUnity.natCard_rootsOfUnity`：natCard_rootsOfUnity (M : Ty
pe*) [CommMonoid M] (n : Nat) [NeZero n] [HasEnoughRootsOfUnity M n] : Nat.card 
(rootsOfUnity n M) = n
· 使用引理 `PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub`：isCauSeq_padicNorm_of_pow_dv
d_sub (f : Nat -> Int) (p : Nat) [Fact p.Prime] (hi : forall i, (p : Int) ^ i ∣ 
f (i + 1) - f i) : IsCauSeq (pad…
· 使用定理 `modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow`：modularCyclotomi
cCharacter.pow_dvd_aux_pow_sub_aux_pow (g : L ≃+* L) (p : Nat) [Fact p.Prime] [f
orall i, HasEnoughRootsOfUnity L (p ^ i)] {i…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cyclotomicCharacter.toFun_apply`：toFun_apply : cyclotomicCharacter.toFun
 p g = PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (aux g <|
 p ^ ·) _ fun i => po…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub`：toZModPow_ofIntSeq_of_pow_dv
d_sub (f : Nat -> Int) (p : Nat) [Fact p.Prime] (hi : forall i, (p : Int) ^ i ∣ 
f (i + 1) - f i) (n : Nat) : (Pa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toZModPow_toFun (n : ℕ) :
    (χ p g).toZModPow n =
      (modularCyclotomicCharacter _
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g).val := by
  rw [toFun_apply]
  refine (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (aux g <| p ^ ·) _ (fun i ↦
    pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) n).trans ?_
  simp [modularCyclotomicCharacter, modularCyclotomicCharacter', modularCyclotomicCharacter.toFun]
/-
**cyclotomicCharacter.toFun_spec** 是 Mathlib 中的一个定理，位于命名空间 `cyclotomicCharacter`
。
形式化陈述：toFun_spec (g : L ≃+* L) {n : Nat} (t : rootsOfUnity (p ^ n) L) : g (t : L
ˣ) = t.1 ^ ((χ p g).toZModPow n).val
参数：g : L ≃+* L；t : rootsOfUnity (p ^ n) L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `HasEnoughRootsOfUnity.natCard_rootsOfUnity`：natCard_rootsOfUnity (M : Ty
pe*) [CommMonoid M] (n : Nat) [NeZero n] [HasEnoughRootsOfUnity M n] : Nat.card 
(rootsOfUnity n M) = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cyclotomicCharacter.toZModPow_toFun`：toZModPow_toFun (n : Nat) : (χ p g)
.toZModPow n = (modularCyclotomicCharacter _ (HasEnoughRootsOfUnity.natCard_root
sOfUnity L (p ^ n)) g).va…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `modularCyclotomicCharacter.spec`：spec (g : L ≃+* L) {t : Lˣ} (ht : t in 
rootsOfUnity n L) : g t = t ^ ((modularCyclotomicCharacter L hn g) : ZMod n).val
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toFun_spec (g : L ≃+* L) {n : ℕ} (t : rootsOfUnity (p ^ n) L) :
    g (t : Lˣ) = t.1 ^ ((χ p g).toZModPow n).val := by
  rw [toZModPow_toFun, ← modularCyclotomicCharacter.spec (ht := t.2)]

end cyclotomicCharacter

variable (L) in
/--
Suppose `L` is a domain containing all `pⁱ`-th primitive roots with `p` a (rational) prime.
If `g` is a ring automorphism of `L`, then `cyclotomicCharacter L p g` is the unique `j : ℤₚ` such
that `g(ζ) = ζ ^ (j mod pⁱ)` for all `pⁱ`-th roots of unity `ζ`.

Note: This is the trivial character when `L` does not contain all `pⁱ`-th primitive roots.
-/
/-
**cyclotomicCharacter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cyclotomicCharacter (p : Nat) [Fact p.Prime] : (L ≃+* L) ->* Int_[p]ˣ
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `L` is a domain containing all `pⁱ`-th primitive roots with `p` a (ratio
nal) prime.
If `g` is a ring automorphism of `L`, then `cyclotomicCharacter L p g` is the un
ique `j : ℤₚ` such
that `g(ζ) = ζ ^ (j mod pⁱ)` for all `pⁱ`-th roots of unity `ζ`.

Note: This is the trivial character when `L` does not contain all `pⁱ`-th primit
ive roots.
-/
noncomputable def cyclotomicCharacter (p : ℕ) [Fact p.Prime] :
    (L ≃+* L) →* ℤ_[p]ˣ := .toHomUnits
  { toFun g := cyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dif_neg H]
    map_mul' f g := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dif_neg H] }
/-
**cyclotomicCharacter.spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cyclotomicCharacter.spec (p : Nat) [Fact p.Prime] {n : Nat} [forall i, Has
EnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) (t : L) (ht : t ^ p ^ n = 1) : g t =
 t ^ ((cyclotomicCharacter L p g).val.toZModPow n).val
参数：p : Nat；p ^ i；g : L ≃+* L；t : L；ht : t ^ p ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cyclotomicCharacter.toFun_spec`：toFun_spec (g : L ≃+* L) {n : Nat} (t : 
rootsOfUnity (p ^ n) L) : g (t : Lˣ) = t.1 ^ ((χ p g).toZModPow n).val
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
-/
theorem cyclotomicCharacter.spec (p : ℕ) [Fact p.Prime] {n : ℕ}
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) (t : L) (ht : t ^ p ^ n = 1) :
    g t = t ^ ((cyclotomicCharacter L p g).val.toZModPow n).val :=
  toFun_spec p g (rootsOfUnity.mkOfPowEq _ ht)
/-
**cyclotomicCharacter.toZModPow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cyclotomicCharacter.toZModPow (p : Nat) [Fact p.Prime] {n : Nat} [forall i
, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) : (cyclotomicCharacter L p g).v
al.toZModPow n = (modularCyclotomicCharacter _ (HasEnoughRootsOfUnity.natCard_ro
otsOfUnity L (p ^ n)) g).val
参数：p : Nat；p ^ i；g : L ≃+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cyclotomicCharacter.toZModPow_toFun`：toZModPow_toFun (n : Nat) : (χ p g)
.toZModPow n = (modularCyclotomicCharacter _ (HasEnoughRootsOfUnity.natCard_root
sOfUnity L (p ^ n)) g).va…
-/
theorem cyclotomicCharacter.toZModPow (p : ℕ) [Fact p.Prime] {n : ℕ}
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) :
    (cyclotomicCharacter L p g).val.toZModPow n =
      (modularCyclotomicCharacter _
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g).val :=
  toZModPow_toFun _ _ _

open IntermediateField in
/-
**cyclotomicCharacter.continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cyclotomicCharacter.continuous (p : Nat) [Fact p.Prime] (K L : Type*) [Fie
ld K] [Field L] [Algebra K L] : Continuous ((cyclotomicCharacter L p).comp (MulS
emiringAction.toRingAut Gal(L/K) L))
参数：p : Nat；K L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `Continuous.of_coeHom_comp`：Continuous.of_coeHom_comp [Group G] [Monoid H
] [TopologicalSpace G] [TopologicalSpace H] [ContinuousInv G] {f : G ->* Hˣ} (hf
 : Continuous (…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `continuous_of_continuousAt_one`：continuous_of_continuousAt_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `GroupFilterBasis.nhds_one_hasBasis`：nhds_one_hasBasis (B : GroupFilterBa
sis G) : HasBasis (@nhds G B.topology 1) (fun V : Set G => V in B) id
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `PadicInt.exists_pow_neg_lt`：exists_pow_neg_lt {ε : Real} (hε : 0 < ε) : 
exists k : Nat, (p : Real) ^ (-(k : Int)) < ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `zpow_le_zpow_right₀`：zpow_le_zpow_right₀ (ha : 1 <= a) (hmn : m <= n) : 
a ^ m <= a ^ n
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 82 条，此处仅展示前 30 条）
-/
lemma cyclotomicCharacter.continuous (p : ℕ) [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Continuous ((cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)) := by
  by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i); swap
  · simp only [cyclotomicCharacter, cyclotomicCharacter.toFun, dif_neg H, MonoidHom.coe_comp]
    exact continuous_const (y := 1)
  have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
  choose ζ hζ using H
  refine Continuous.of_coeHom_comp ?_
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, (galGroupBasis K L).nhds_one_hasBasis.tendsto_iff
    (Metric.nhds_basis_ball (α := ℤ_[p]) (x := 1))]
  intro ε hε
  obtain ⟨k, hk', hk⟩ : ∃ k : ℕ, k ≠ 0 ∧ p ^ (-k : ℤ) < ε := by
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    exact ⟨k + 1, by simp, lt_of_le_of_lt (by gcongr <;> simp [‹Fact p.Prime›.1.one_le]) hk⟩
  refine ⟨_, ⟨_, ⟨(K⟮ζ k⟯), adjoin.finiteDimensional ?_, rfl⟩, rfl⟩, ?_⟩
  · exact ((hζ k).isIntegral (Nat.pos_of_neZero _)).tower_top
  · intro σ hσ
    refine lt_of_le_of_lt ?_ hk
    dsimp
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, map_one, cyclotomicCharacter.toZModPow,
      sub_eq_zero, eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := ((hζ k).isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ ⟨ζ k ^ i, pow_mem (mem_adjoin_simple_self K (ζ k)) _⟩
    · exact (one_lt_pow₀ ‹Fact p.Prime›.1.one_lt hk').ne'
