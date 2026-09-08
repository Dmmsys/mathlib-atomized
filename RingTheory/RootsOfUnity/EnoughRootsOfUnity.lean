/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Commutative monoids with enough roots of unity

We define a typeclass `HasEnoughRootsOfUnity M n` for a commutative monoid `M` and
a natural number `n` that asserts that `M` contains a primitive `n`th root of unity
and that the group of `n`th roots of unity in `M` is cyclic. Such monoids are suitable
targets for homomorphisms from groups of exponent (dividing) `n`; for example,
the homomorphisms can then be used to separate elements of the source group.
-/

public section

/-- This is a type class recording that a commutative monoid `M` contains primitive `n`th
roots of unity and such that the group of `n`th roots of unity is cyclic.

Such monoids are suitable targets in the context of duality statements for groups
of exponent `n`. -/
/-
**HasEnoughRootsOfUnity** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [CommMonoid M] → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a type class recording that a commutative monoid `M` contains primitive 
`n`th
roots of unity and such that the group of `n`th roots of unity is cyclic.

Such monoids are suitable targets in the context of duality statements for group
s
of exponent `n`.
-/
class HasEnoughRootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) where
  prim : ∃ m : M, IsPrimitiveRoot m n
  cyc : IsCyclic <| rootsOfUnity n M

namespace HasEnoughRootsOfUnity

/-
**HasEnoughRootsOfUnity.exists_primitiveRoot** 是 Mathlib 中的一个引理，位于命名空间 `HasEnoug
hRootsOfUnity`。
形式化陈述：exists_primitiveRoot (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRootsO
fUnity M n] : exists ζ : M, IsPrimitiveRoot ζ n
参数：M : Type*；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasEnoughRootsOfUnity.prim`：∀ {M : Type u_1} {inst : CommMonoid M} {n : 
ℕ} [self : HasEnoughRootsOfUnity M n], ∃ m, IsPrimitiveRoot m n
-/
lemma exists_primitiveRoot (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    ∃ ζ : M, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim
/-
**HasEnoughRootsOfUnity.rootsOfUnity_isCyclic** 是 Mathlib 中的一个实例，位于命名空间 `HasEnou
ghRootsOfUnity`。
形式化陈述：rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRoots
OfUnity M n] : IsCyclic (rootsOfUnity n M)
参数：M : Type*；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HasEnoughRootsOfUnity.cyc`：∀ {M : Type u_1} {inst : CommMonoid M} {n : ℕ
} [self : HasEnoughRootsOfUnity M n], IsCyclic ↥(rootsOfUnity n M)
-/
instance rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    IsCyclic (rootsOfUnity n M) :=
  HasEnoughRootsOfUnity.cyc

/-- If `HasEnoughRootsOfUnity M n` and `m ∣ n`, then also `HasEnoughRootsOfUnity M m`. -/
/-
**HasEnoughRootsOfUnity.of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `HasEnoughRootsOfUnity`
。
形式化陈述：of_dvd (M : Type*) [CommMonoid M] {m n : Nat} [NeZero n] (hmn : m ∣ n) [Ha
sEnoughRootsOfUnity M n] : HasEnoughRootsOfUnity M m where prim
参数：M : Type*；hmn : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasEnoughRootsOfUnity.exists_primitiveRoot`：exists_primitiveRoot (M : Ty
pe*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] : exists ζ : M, IsPrim
itiveRoot ζ n
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Subgroup.isCyclic_of_le`：Subgroup.isCyclic_of_le {H H' : Subgroup G} (h 
: H <= H') [IsCyclic H'] : IsCyclic H
· 使用定理 `rootsOfUnity_le_of_dvd`：rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnit
y k M <= rootsOfUnity l M

--- 原说明 ---
If `HasEnoughRootsOfUnity M n` and `m ∣ n`, then also `HasEnoughRootsOfUnity M m
`.
-/
lemma of_dvd (M : Type*) [CommMonoid M] {m n : ℕ} [NeZero n] (hmn : m ∣ n)
    [HasEnoughRootsOfUnity M n] :
    HasEnoughRootsOfUnity M m where
  prim :=
    have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
  cyc := Subgroup.isCyclic_of_le <| rootsOfUnity_le_of_dvd hmn

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` is finite. -/
/-
**HasEnoughRootsOfUnity.finite_rootsOfUnity** 是 Mathlib 中的一个实例，位于命名空间 `HasEnough
RootsOfUnity`。
形式化陈述：finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : Nat) [NeZero n] [HasEn
oughRootsOfUnity M n] : Finite rootsOfUnity n M
参数：M : Type*；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_eq_zpow_emod'`：zpow_eq_zpow_emod' {x : G} (m : Int) {n : Nat} (h : 
x ^ n = 1) : x ^ m = x ^ (m % (n : Int))

--- 原说明 ---
If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` is finite.
-/
instance finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Finite <| rootsOfUnity n M := by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : ℤ)
  refine Finite.of_surjective f fun x ↦ ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp <| hg x
  refine ⟨k, ?_⟩
  simpa only [ZMod.natCast_val, ← hk, f, ZMod.coe_intCast] using (zpow_eq_zpow_emod' k hg').symm

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` (is cyclic and) has order `n`. -/
/-
**HasEnoughRootsOfUnity.natCard_rootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 `HasEnoug
hRootsOfUnity`。
形式化陈述：natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : Nat) [NeZero n] [HasE
noughRootsOfUnity M n] : Nat.card (rootsOfUnity n M) = n
参数：M : Type*；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasEnoughRootsOfUnity.exists_primitiveRoot`：exists_primitiveRoot (M : Ty
pe*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] : exists ζ : M, IsPrim
itiveRoot ζ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用引理 `Subgroup.orderOf_mk`：orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = o
rderOf a
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G

--- 原说明 ---
If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` (is cyclic and) has order `n`.
-/
lemma natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Nat.card (rootsOfUnity n M) = n := by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit NeZero.out).unit_spec, orderOf_units]
    let ζ' : rootsOfUnity n M := ⟨(h.isUnit NeZero.out).unit, ?_⟩
    · rw [← Subgroup.orderOf_mk]
      exact Monoid.order_dvd_exponent ζ'
    simp only [mem_rootsOfUnity]
    rw [← Units.val_inj, Units.val_pow_eq_pow_val, IsUnit.unit_spec, h.pow_eq_one, Units.val_one]
/-
**HasEnoughRootsOfUnity.of_card_le** 是 Mathlib 中的一个引理，位于命名空间 `HasEnoughRootsOfUn
ity`。
形式化陈述：of_card_le {R : Type*} [CommRing R] [IsDomain R] {n : Nat} [NeZero n] (h :
 n <= Nat.card (rootsOfUnity n R)) : HasEnoughRootsOfUnity R n where prim
参数：h : n <= Nat.card (rootsOfUnity n R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot`：∀ {R : Type u_4} [inst 
: CommRing R] [IsDomain R] {n : ℕ} [NeZero n],   Nat.card ↥(rootsOfUnity n R) = 
n ↔ ∃ ζ, IsPrimitiveRoot ζ n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `card_rootsOfUnity`：card_rootsOfUnity : Nat.card (rootsOfUnity k R) <= k
-/
lemma of_card_le {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (h : n ≤ Nat.card (rootsOfUnity n R)) : HasEnoughRootsOfUnity R n where
  prim := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (le_antisymm (card_rootsOfUnity R n) h)
  cyc := rootsOfUnity.isCyclic R n

end HasEnoughRootsOfUnity

/-
**MulEquiv.hasEnoughRootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.hasEnoughRootsOfUnity {n : Nat} [NeZero n] {M N : Type*} [CommMon
oid M] [CommMonoid N] [hm : HasEnoughRootsOfUnity M n] (e : rootsOfUnity n M ≃* 
rootsOfUnity n N) : HasEnoughRootsOfUnity N n where prim
参数：e : rootsOfUnity n M ≃* rootsOfUnity n N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasEnoughRootsOfUnity.prim`：∀ {M : Type u_1} {inst : CommMonoid M} {n : 
ℕ} [self : HasEnoughRootsOfUnity M n], ∃ m, IsPrimitiveRoot m n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.coe_units_iff`：coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot 
(ζ : M) k ↔ IsPrimitiveRoot ζ k
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `IsPrimitiveRoot.coe_submonoidClass_iff`：coe_submonoidClass_iff {M B : Ty
pe*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {N : B} {ζ : N} : IsPrimi
tiveRoot (ζ : M) k ↔ IsPrimi…
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
lemma MulEquiv.hasEnoughRootsOfUnity {n : ℕ} [NeZero n] {M N : Type*} [CommMonoid M]
    [CommMonoid N] [hm : HasEnoughRootsOfUnity M n] (e : rootsOfUnity n M ≃* rootsOfUnity n N) :
    HasEnoughRootsOfUnity N n where
  prim := by
    obtain ⟨m, hm⟩ := hm.prim
    use (e hm.toRootsOfUnity).val.val
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
    refine .map_of_injective ?_ e.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
  cyc := isCyclic_of_surjective e e.surjective

section cyclic

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into the
group of units of a ring `M` with all roots of unity is isomorphic to `G` -/
/-
**IsCyclic.monoidHom_equiv_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G] [IsCy
clic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] : Nonempty ((G ->*
 Mˣ) ≃* G)
参数：G M : Type*；Nat.card G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasEnoughRootsOfUnity.natCard_rootsOfUnity`：natCard_rootsOfUnity (M : Ty
pe*) [CommMonoid M] (n : Nat) [NeZero n] [HasEnoughRootsOfUnity M n] : Nat.card 
(rootsOfUnity n M) = n
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用引理 `IsCyclic.monoidHom_mulEquiv_rootsOfUnity`：monoidHom_mulEquiv_rootsOfUnit
y (G : Type*) [CommGroup G] [IsCyclic G] (G' : Type*) [CommGroup G'] : Nonempty 
(G ->* G') ≃* rootsOfUnity (Na…

--- 原说明 ---
The group of group homomorphisms from a finite cyclic group `G` of order `n` int
o the
group of units of a ring `M` with all roots of unity is isomorphic to `G`
-/
lemma IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G →* Mˣ) ≃* G) := by
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
  exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G)) |>.trans (mulEquivOfCyclicCardEq hord)⟩

end cyclic

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [CommMonoid M] : HasEnoughRootsOfUnity M 1 where
  prim := ⟨1, by simp⟩
  cyc := isCyclic_of_subsingleton
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G M : Type*} [Group G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    Finite (G →* Mˣ) := by
  let S := rootsOfUnity (Monoid.exponent G) M
  have : Finite (G →* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective S.subtype.comp fun f ↦ ?_
  have H a : f a ∈ S := by
    rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ by simp⟩
