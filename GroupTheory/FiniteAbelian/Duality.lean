/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Duality for finite abelian groups

Let `G` be a finite abelian group.

For `M` a commutative monoid that has enough `n`th roots of unity, where `n` is the exponent of `G`,
the main results in this file are:
* `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: Homomorphisms `G →* Mˣ` separate
  elements of `G`.
* `CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity`: `G` is isomorphic to `G →* Mˣ`.
* `CommGroup.monoidHomMonoidHomEquiv`: `G` is isomorphic to its double dual `(G →* Mˣ) →* Mˣ`.
* `CommGroup.subgroupOrderIsoSubgroupMonoidHom`: the order reversing bijection that sends a
  subgroup of `G` to its dual subgroup in `G →* Mˣ`.
-/

@[expose] public section

namespace CommGroup

open MonoidHom

/-
**CommGroup.dvd_exponent** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma dvd_exponent {ι G : Type*} [Monoid G] {n : ι → ℕ}
    (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent G := by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

variable (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]

private
/-
**CommGroup.exists_apply_ne_one_aux** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：exists_apply_ne_one_aux (H : forall n : Nat, n ∣ Monoid.exponent G -> fora
ll a : ZMod n, a != 0 -> exists φ : Multiplicative (ZMod n) ->* M, φ (.ofAdd a) 
!= 1) {a : G} (ha : a != 1) : exists φ : G ->* M, φ a != 1
参数：H : forall n : Nat, n ∣ Monoid.exponent G -> forall a : ZMod n, a != 0 -> exi
sts φ : Multiplicative (ZMod n) ->* M, φ (.ofAdd a) != 1；ha : a != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_apply_ne_one_aux
    (H : ∀ n : ℕ, n ∣ Monoid.exponent G → ∀ a : ZMod n, a ≠ 0 →
      ∃ φ : Multiplicative (ZMod n) →* M, φ (.ofAdd a) ≠ 1)
    {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* M, φ a ≠ 1 := by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let e := h.some
  obtain ⟨i, hi⟩ : ∃ i : ι, e a i ≠ 1 := by
    contrapose! ha
    exact (MulEquiv.map_eq_one_iff e).mp <| funext ha
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) ((e a i).toAdd) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) ↦ Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using! hφi

variable [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- If `G` is a finite commutative group of exponent `n` and `M` is a commutative monoid
with enough `n`th roots of unity, then for each `a ≠ 1` in `G`, there exists a
group homomorphism `φ : G → Mˣ` such that `φ a ≠ 1`. -/
/-
**CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个定理，位于命名
空间 `CommGroup`。
形式化陈述：exists_apply_ne_one_of_hasEnoughRootsOfUnity {a : G} (ha : a != 1) : exist
s φ : G ->* Mˣ, φ a != 1
参数：ha : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.FiniteAbelian.Duality.0.CommGroup.exists_ap
ply_ne_one_aux`：∀ (G : Type u_1) (M : Type u_2) [inst : CommGroup G] [Finite G] 
[inst_2 : CommMonoid M],   (∀ (n : ℕ), n ∣ Monoid.exponent G → ∀ (a : ZMod n…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.eq_zero_of_zero_dvd`：∀ {a : ℕ}, 0 ∣ a → a = 0
· 使用引理 `HasEnoughRootsOfUnity.of_dvd`：of_dvd (M : Type*) [CommMonoid M] {m n : N
at} [NeZero n] (hmn : m ∣ n) [HasEnoughRootsOfUnity M n] : HasEnoughRootsOfUnity
 M m where prim
· 使用引理 `ZMod.exists_monoidHom_apply_ne_one`：ZMod.exists_monoidHom_apply_ne_one {
M : Type*} [CommMonoid M] {n : Nat} [NeZero n] (hG : exists ζ : M, IsPrimitiveRo
ot ζ n) {a : ZMod n} (ha…
· 使用引理 `HasEnoughRootsOfUnity.exists_primitiveRoot`：exists_primitiveRoot (M : Ty
pe*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] : exists ζ : M, IsPrim
itiveRoot ζ n

--- 原说明 ---
If `G` is a finite commutative group of exponent `n` and `M` is a commutative mo
noid
with enough `n`th roots of unity, then for each `a ≠ 1` in `G`, there exists a
group homomorphism `φ : G → Mˣ` such that `φ a ≠ 1`.
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* Mˣ, φ a ≠ 1 := by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ ↦ ?_) ha
  have : NeZero n := ⟨fun H ↦ NeZero.ne _ <| Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

variable {M} in
@[simp]
/-
**CommGroup.forall_apply_eq_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：forall_apply_eq_apply_iff {g g' : G} : (forall φ : G ->* Mˣ, φ g = φ g') ↔
 g = g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`：exists_apply_ne_
one_of_hasEnoughRootsOfUnity {a : G} (ha : a != 1) : exists φ : G ->* Mˣ, φ a !=
 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem forall_apply_eq_apply_iff {g g' : G} :
    (∀ φ : G →* Mˣ, φ g = φ g') ↔ g = g' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simpa [← not_forall, not_imp_not, mul_inv_eq_one, h] using
    exists_apply_ne_one_of_hasEnoughRootsOfUnity G M (a := g * g'⁻¹)

/-- A finite commutative group `G` is (noncanonically) isomorphic to the group `G →* Mˣ`
when `M` is a commutative monoid with enough `n`th roots of unity, where `n` is the exponent
of `G`. -/
/-
**CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个定理，位于命名空
间 `CommGroup`。
形式化陈述：monoidHom_mulEquiv_of_hasEnoughRootsOfUnity : Nonempty ((G ->* Mˣ) ≃* G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.equiv_prod_multiplicative_zmod_of_finite`：equiv_prod_multiplic
ative_zmod_of_finite (G : Type*) [CommGroup G] [Finite G] : exists (ι : Type) (_
 : Fintype ι) (n : ι -> Nat), (forall (i…
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_multiplicative`：∀ (α : Type u_1) [inst : Fintype α], Fintyp
e.card (Multiplicative α) = Fintype.card α
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `_private.Mathlib.GroupTheory.FiniteAbelian.Duality.0.CommGroup.dvd_expon
ent`：∀ {ι : Type u_1} {G : Type u_2} [inst : Monoid G] {n : ι → ℕ} (e : G ≃* ((i
 : ι) → Multiplicative (ZMod (n i))))   (i : ι), n i ∣ Monoid.exp…
· 使用引理 `HasEnoughRootsOfUnity.of_dvd`：of_dvd (M : Type*) [CommMonoid M] {m n : N
at} [NeZero n] (hmn : m ∣ n) [HasEnoughRootsOfUnity M n] : HasEnoughRootsOfUnity
 M m where prim
· 使用引理 `IsCyclic.monoidHom_equiv_self`：IsCyclic.monoidHom_equiv_self (G M : Type
*) [CommGroup G] [Finite G] [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M
 (Nat.card G)] : No…
· 使用定理 `instFiniteMultiplicative`：∀ {α : Type u} [Finite α], Finite (Multiplicat
ive α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A finite commutative group `G` is (noncanonically) isomorphic to the group `G →*
 Mˣ`
when `M` is a commutative monoid with enough `n`th roots of unity, where `n` is 
the exponent
of `G`.
-/
theorem monoidHom_mulEquiv_of_hasEnoughRootsOfUnity : Nonempty ((G →* Mˣ) ≃* G) := by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Mˣ
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  have inst i : HasEnoughRootsOfUnity M <| Nat.card <| Multiplicative <| ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
  exact ⟨e.monoidHomCongrLeft.trans <| e'.trans <| .trans (.piCongrRight E) e.symm⟩
/-
**CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 `C
ommGroup`。
形式化陈述：card_monoidHom_of_hasEnoughRootsOfUnity : Nat.card (G ->* Mˣ) = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`：monoidHom_mulEqui
v_of_hasEnoughRootsOfUnity : Nonempty ((G ->* Mˣ) ≃* G)
-/
theorem card_monoidHom_of_hasEnoughRootsOfUnity :
    Nat.card (G →* Mˣ) = Nat.card G :=
  Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

variable {G}

/--
Let `G` be a finite commutative group and let `H` be a subgroup. If `M` is a commutative monoid
such that `G →* Mˣ` and `H →* Mˣ` are both finite (this is the case for example if `M` is a
commutative domain) and with enough `n`th roots of unity, where `n` is the exponent
of `G`, then any homomorphism `H →* Mˣ` can be extended to an homomorphism `G →* Mˣ`.
-/
/-
**CommGroup._root_.MonoidHom.domRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `C
ommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be a finite commutative group and let `H` be a subgroup. If `M` is a com
mutative monoid
such that `G →* Mˣ` and `H →* Mˣ` are both finite (this is the case for example 
if `M` is a
commutative domain) and with enough `n`th roots of unity, where `n` is the expon
ent
of `G`, then any homomorphism `H →* Mˣ` can be extended to an homomorphism `G →*
 Mˣ`.
-/
theorem _root_.MonoidHom.domRestrict_surjective (H : Subgroup G) :
    Function.Surjective (MonoidHom.domRestrictHom H Mˣ) := by
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
    hM.of_dvd M <| Monoid.exponent_submonoid_dvd H.toSubmonoid
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_quotient_dvd H
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity,
    H.card_eq_card_quotient_mul_card_subgroup,
    mul_div_cancel_right₀ _ (Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero),
    ← card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) M,
    Nat.card_congr (domRestrictHomKerEquiv Mˣ H).toEquiv]

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrict_surjective := _root_.MonoidHom.domRestrict_surjective

@[simp]
/-
**CommGroup.forall_monoidHom_apply_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommGro
up`。
形式化陈述：forall_monoidHom_apply_eq_one_iff (H : Subgroup G) (x : G) : (forall (φ : 
G ->* Mˣ), (forall y in H, φ y = 1) -> φ x = 1) ↔ x in H
参数：H : Subgroup G；x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用引理 `HasEnoughRootsOfUnity.of_dvd`：of_dvd (M : Type*) [CommMonoid M] {m n : N
at} [NeZero n] (hmn : m ∣ n) [HasEnoughRootsOfUnity M n] : HasEnoughRootsOfUnity
 M m where prim
· 使用定理 `Group.exponent_quotient_dvd`：Group.exponent_quotient_dvd (H : Subgroup G
) [H.Normal] : Monoid.exponent (G ⧸ H) ∣ Monoid.exponent G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CommGroup.forall_apply_eq_apply_iff`：forall_apply_eq_apply_iff {g g' : G
} : (forall φ : G ->* Mˣ, φ g = φ g') ↔ g = g'
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem forall_monoidHom_apply_eq_one_iff (H : Subgroup G) (x : G) :
    (∀ (φ : G →* Mˣ), (∀ y ∈ H, φ y = 1) → φ x = 1) ↔ x ∈ H := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_quotient_dvd H
  refine ⟨fun h ↦ ?_, fun hx φ hφ ↦ hφ x hx⟩
  simp only [← QuotientGroup.eq_one_iff, ← forall_apply_eq_apply_iff _ (M := M), map_one] at h ⊢
  exact fun φ ↦ h (φ.comp (QuotientGroup.mk' H)) fun y hy ↦ hy φ
/-
**CommGroup.card_domRestrictHom_ker** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：card_domRestrictHom_ker (H : Subgroup G) : Nat.card (domRestrictHom H Mˣ).
ker = Nat.card (G ⧸ H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用引理 `HasEnoughRootsOfUnity.of_dvd`：of_dvd (M : Type*) [CommMonoid M] {m n : N
at} [NeZero n] (hmn : m ∣ n) [HasEnoughRootsOfUnity M n] : HasEnoughRootsOfUnity
 M m where prim
· 使用定理 `Group.exponent_quotient_dvd`：Group.exponent_quotient_dvd (H : Subgroup G
) [H.Normal] : Monoid.exponent (G ⧸ H) ∣ Monoid.exponent G
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`：card_monoidHom_of_has
EnoughRootsOfUnity : Nat.card (G ->* Mˣ) = Nat.card G
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
-/
theorem card_domRestrictHom_ker (H : Subgroup G) :
    Nat.card (domRestrictHom H Mˣ).ker = Nat.card (G ⧸ H) := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_quotient_dvd H
  rw [Nat.card_congr (MonoidHom.domRestrictHomKerEquiv Mˣ H).toEquiv,
    card_monoidHom_of_hasEnoughRootsOfUnity]

@[deprecated (since := "2026-07-19")] alias card_restrictHom_ker := card_domRestrictHom_ker

variable (G) in
/--
The `MulEquiv` between the double dual `(G →* Mˣ) →* Mˣ` of a finite commutative group `G`
and itself  where `M` is a commutative monoid with enough `n`th roots of unity, where `n` is
the exponent of `G`.
The image `g` of `η : (G →* Mˣ) →* Mˣ` is such that, for all `φ : G →* Mˣ`, we have `φ g = η g`,
see `CommGroup.apply_monoidHomMonoidHomEquiv`.
-/
@[simps! symm_apply_apply]
/-
**CommGroup.monoidHomMonoidHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommGroup`。
形式化陈述：monoidHomMonoidHomEquiv : ((G ->* Mˣ) ->* Mˣ) ≃* G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MulEquiv` between the double dual `(G →* Mˣ) →* Mˣ` of a finite commutative
 group `G`
and itself  where `M` is a commutative monoid with enough `n`th roots of unity, 
where `n` is
the exponent of `G`.
The image `g` of `η : (G →* Mˣ) →* Mˣ` is such that, for all `φ : G →* Mˣ`, we h
ave `φ g = η g`,
see `CommGroup.apply_monoidHomMonoidHomEquiv`.
-/
noncomputable def monoidHomMonoidHomEquiv :
    ((G →* Mˣ) →* Mˣ) ≃* G :=
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G →* Mˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g ↦ MonoidHom.mk ⟨fun φ ↦ φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h ↦ ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity]))
    (fun _ _ ↦ by ext; simp)).symm

@[simp]
/-
**CommGroup.apply_monoidHomMonoidHomEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：apply_monoidHomMonoidHomEquiv (φ : G ->* Mˣ) (η : (G ->* Mˣ) ->* Mˣ) : φ (
monoidHomMonoidHomEquiv G M η) = η φ
参数：φ : G ->* Mˣ；η : (G ->* Mˣ) ->* Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply`：∀ (G : Type u_1) (M 
: Type u_2) [inst : CommGroup G] [inst_1 : Finite G] [inst_2 : CommMonoid M]   [
hM : HasEnoughRootsOfUnity M (Monoid.exp…
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem apply_monoidHomMonoidHomEquiv (φ : G →* Mˣ) (η : (G →* Mˣ) →* Mˣ) :
    φ (monoidHomMonoidHomEquiv G M η) = η φ := by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G M (monoidHomMonoidHomEquiv G M η) φ,
    MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
variable (G) in
/--
The order reversing bijection that sends a subgroup of `G` to its dual subgroup in `G →* Mˣ`
where `G` is a finite commutative group and `M` is a commutative monoid with enough `n`th roots of
unity, where `n` is the exponent of `G`.
-/
/-
**CommGroup.subgroupOrderIsoSubgroupMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CommGro
up`。
形式化陈述：subgroupOrderIsoSubgroupMonoidHom : Subgroup G ≃o (Subgroup (G ->* Mˣ))ᵒᵈ 
where toFun H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order reversing bijection that sends a subgroup of `G` to its dual subgroup 
in `G →* Mˣ`
where `G` is a finite commutative group and `M` is a commutative monoid with eno
ugh `n`th roots of
unity, where `n` is the exponent of `G`.
-/
noncomputable def subgroupOrderIsoSubgroupMonoidHom : Subgroup G ≃o (Subgroup (G →* Mˣ))ᵒᵈ where
  toFun H := OrderDual.toDual (domRestrictHom H Mˣ).ker
  invFun Φ := (monoidHomMonoidHomEquiv G M).mapSubgroup (domRestrictHom Φ.ofDual Mˣ).ker
  map_rel_iff' {H₁} {H₂} := by
    simp_rw [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual,
      SetLike.le_def, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff]
    grind [forall_monoidHom_apply_eq_one_iff M H₂]
  left_inv H := by
    ext x
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
    simp
  right_inv Φ := by
    have : HasEnoughRootsOfUnity M (Monoid.exponent (G →* Mˣ)) := by
      rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
    ext φ
    rw [OrderDual.ofDual_toDual, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff]
    simp

@[simp]
/-
**CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CommGroup`。
形式化陈述：mem_subgroupOrderIsoSubgroupMonoidHom_iff (H : Subgroup G) (φ : G ->* Mˣ) 
: φ in (subgroupOrderIsoSubgroupMonoidHom G M H).ofDual ↔ forall g in H, φ g = 1
参数：H : Subgroup G；φ : G ->* Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulEquiv.mapSubgroup_apply`：∀ {G : Type u_1} [inst : Group G] {H : Type 
u_6} [inst_1 : Group H] (f : G ≃* H) (H_1 : Subgroup G),   f.mapSubgroup H_1 = S
ubgroup.map (↑f)…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `RelIso.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop}
 {s : β → β → Prop} (toEquiv toEquiv_1 : α ≃ β)   (e_toEquiv : toEquiv = toEquiv
_1) (map_r…
· 使用定理 `MonoidHom.domRestrictHom_apply`：∀ {M : Type u_1} [inst : MulOneClass M] 
{S : Type u_5} [inst_1 : SetLike S M] [inst_2 : SubmonoidClass S M] (M' : S)   (
A : Type u_6) [inst_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subgroupOrderIsoSubgroupMonoidHom_iff (H : Subgroup G) (φ : G →* Mˣ) :
    φ ∈ (subgroupOrderIsoSubgroupMonoidHom G M H).ofDual ↔ ∀ g ∈ H, φ g = 1 := by
  simp [subgroupOrderIsoSubgroupMonoidHom]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CommGroup`。
形式化陈述：mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff (Φ : Subgroup (G ->* Mˣ)) (
g : G) : g in (subgroupOrderIsoSubgroupMonoidHom G M).symm (OrderDual.toDual Φ) 
↔ forall φ in Φ, φ g = 1
参数：Φ : Subgroup (G ->* Mˣ)；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.domRestrictHom_apply`：∀ {M : Type u_1} [inst : MulOneClass M] 
{S : Type u_5} [inst_1 : SetLike S M] [inst_2 : SubmonoidClass S M] (M' : S)   (
A : Type u_6) [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply`：∀ (G : Type u_1) (M 
: Type u_2) [inst : CommGroup G] [inst_1 : Finite G] [inst_2 : CommMonoid M]   [
hM : HasEnoughRootsOfUnity M (Monoid.exp…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff (Φ : Subgroup (G →* Mˣ)) (g : G) :
    g ∈ (subgroupOrderIsoSubgroupMonoidHom G M).symm (OrderDual.toDual Φ) ↔ ∀ φ ∈ Φ, φ g = 1 := by
  simp_rw [subgroupOrderIsoSubgroupMonoidHom, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff,
    monoidHomMonoidHomEquiv_symm_apply_apply]

/-- The cardinality of the dual subgroup of `G →* Mˣ` associated to a subgroup `H` of `G`
equals the index of `H` in `G`. -/
/-
**CommGroup.card_subgroupOrderIsoSubgroupMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Co
mmGroup`。
形式化陈述：card_subgroupOrderIsoSubgroupMonoidHom (H : Subgroup G) : Nat.card (subgro
upOrderIsoSubgroupMonoidHom G M H).ofDual = Nat.card (G ⧸ H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.card_domRestrictHom_ker`：card_domRestrictHom_ker (H : Subgroup
 G) : Nat.card (domRestrictHom H Mˣ).ker = Nat.card (G ⧸ H)

--- 原说明 ---
The cardinality of the dual subgroup of `G →* Mˣ` associated to a subgroup `H` o
f `G`
equals the index of `H` in `G`.
-/
theorem card_subgroupOrderIsoSubgroupMonoidHom (H : Subgroup G) :
    Nat.card (subgroupOrderIsoSubgroupMonoidHom G M H).ofDual = Nat.card (G ⧸ H) :=
  card_domRestrictHom_ker _ _

end CommGroup

