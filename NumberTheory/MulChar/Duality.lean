/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

## Main results

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
  (noncanonically) isomorphic to `Mˣ`.

* `MulChar.mulCharEquiv`: the `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M`
  and `Mˣ`.

* `MulChar.subgroupOrderIsoSubgroupMulChar`: The order reversing bijection that sends a
  subgroup of `Mˣ` to its dual subgroup in `MulChar M R`.

-/

@[expose] public section

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

/-
**MulChar.finite** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `instFiniteMonoidHomUnits`：∀ {R : Type u_4} [inst : CommRing R] [IsDomain
 R] {L : Type u_7} [inst_2 : LeftCancelMonoid L] [Finite L],   Finite (L →* Rˣ)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := .of_equiv _ equivToUnitHom.symm
/-
**MulChar.exists_apply_ne_one_iff_exists_monoidHom** 是 Mathlib 中的一个引理，位于命名空间 `Mu
lChar`。
形式化陈述：exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) : (exists χ : MulChar M 
R, χ a != 1) ↔ exists φ : Mˣ ->* Rˣ, φ a != 1
参数：a : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.coe_toUnitHom`：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.t
oUnitHom a) = χ a
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.equivToUnitHom_symm_coe`：equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ
) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a
-/
lemma exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) :
    (∃ χ : MulChar M R, χ a ≠ 1) ↔ ∃ φ : Mˣ →* Rˣ, φ a ≠ 1 := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

variable (M R)
variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- If `M` is a finite commutative monoid and `R` is a ring that has enough roots of unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative character `χ : M → R` such that
`χ a ≠ 1`. -/
/-
**MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间
 `MulChar`。
形式化陈述：exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : 
a != 1) : exists χ : MulChar M R, χ a != 1
参数：ha : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MulChar.exists_apply_ne_one_iff_exists_monoidHom`：exists_apply_ne_one_if
f_exists_monoidHom (a : Mˣ) : (exists χ : MulChar M R, χ a != 1) ↔ exists φ : Mˣ
 ->* Rˣ, φ a != 1
· 使用定理 `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`：exists_apply_ne_
one_of_hasEnoughRootsOfUnity {a : G} (ha : a != 1) : exists φ : G ->* Mˣ, φ a !=
 1
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1

--- 原说明 ---
If `M` is a finite commutative monoid and `R` is a ring that has enough roots of
 unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative character `χ : M → R
` such that
`χ a ≠ 1`.
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : a ≠ 1) :
    ∃ χ : MulChar M R, χ a ≠ 1 := by
  by_cases hu : IsUnit a
  · refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose ha
    rw [← hu.unit_spec, ha, Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

/-- The group of `R`-valued multiplicative characters on a finite commutative monoid `M` is
(noncanonically) isomorphic to its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
/-
**MulChar.mulEquiv_units** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`：monoidHom_mulEqui
v_of_hasEnoughRootsOfUnity : Nonempty ((G ->* Mˣ) ≃* G)
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ

--- 原说明 ---
The group of `R`-valued multiplicative characters on a finite commutative monoid
 `M` is
(noncanonically) isomorphic to its unit group `Mˣ` when `R` is a ring that has e
nough roots
of unity.
-/
lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

/-- The cardinality of the group of `R`-valued multiplicative characters on a finite commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
/-
**MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 
`MulChar`。
形式化陈述：card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat
.card Mˣ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用引理 `MulChar.mulEquiv_units`：mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ)

--- 原说明 ---
The cardinality of the group of `R`-valued multiplicative characters on a finite
 commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that ha
s enough roots
of unity.
-/
lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv


/--
Let `N` be a submonoid of `M` group and let `R` be a ring with enough roots of unity.
Then any `R`-value multiplicative character of `N` can be extended to a multiplicative
character of `M`.
-/
/-
**MulChar.domRestrictHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：domRestrictHom_surjective (N : Submonoid M) : Function.Surjective (MulChar
.domRestrictHom N R)
参数：N : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHom.domRestrict_surjective`：∀ {G : Type u_1} (M : Type u_2) [inst 
: CommGroup G] [Finite G] [inst_2 : CommMonoid M]   [hM : HasEnoughRootsOfUnity 
M (Monoid.exponent G)]…
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.domRestrictHom_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {S 
: Type u_3} [inst_1 : SetLike S R] [inst_2 : SubmonoidClass S R] (T : S)   (R'' 
: Type u_4) [inst_…
· 使用定理 `MulChar.domRestrict_ofUnitHom`：domRestrict_ofUnitHom (f : Rˣ ->* R'ˣ) (S
 : Submonoid R) : domRestrict S (ofUnitHom f) = ofUnitHom ((f.domRestrict S.unit
s).comp S.unitsEqui…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MonoidHom.domRestrictHom_apply`：∀ {M : Type u_1} [inst : MulOneClass M] 
{S : Type u_5} [inst_1 : SetLike S M] [inst_2 : SubmonoidClass S M] (M' : S)   (
A : Type u_6) [inst_…
· 使用定理 `MulChar.equivToUnitHom_symm_coe`：equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ
) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `N` be a submonoid of `M` group and let `R` be a ring with enough roots of u
nity.
Then any `R`-value multiplicative character of `N` can be extended to a multipli
cative
character of `M`.
-/
theorem domRestrictHom_surjective (N : Submonoid M) :
    Function.Surjective (MulChar.domRestrictHom N R) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).domRestrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ ↦ ?_⟩
  rw [MonoidHom.domRestrictHom_apply] at hψ
  rw [domRestrictHom_apply, domRestrict_ofUnitHom]
  simp [hψ]

@[deprecated (since := "2026-07-19")] alias restrictHom_surjective := domRestrictHom_surjective

/-- The `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M` and `Mˣ`.
The image `m` of `η : MulChar (MulChar M R) R` is such that, for all `R`-valued multiplicative
character `χ` of `M`, we have `χ m = η χ`, see `MulChar.apply_mulCharEquiv`.
-/
/-
**MulChar.mulCharEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M` and `Mˣ`
.
The image `m` of `η : MulChar (MulChar M R) R` is such that, for all `R`-valued 
multiplicative
character `χ` of `M`, we have `χ m = η χ`, see `MulChar.apply_mulCharEquiv`.
-/
noncomputable def mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
  mulEquivToUnitHom.trans <| toUnits.monoidHomCongrLeft.symm.trans <|
    mulEquivToUnitHom.monoidHomCongrLeft.trans <| CommGroup.monoidHomMonoidHomEquiv Mˣ R

variable {M R}

@[simp]
/-
**MulChar.mulCharEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：mulCharEquiv_symm_apply_apply (m : Mˣ) (χ : MulChar M R) : (mulCharEquiv M
 R).symm m χ = χ m
参数：m : Mˣ；χ : MulChar M R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
· 使用定理 `MulChar.mulEquivToUnitHom_apply`：∀ {R : Type u_1} [inst : CommMonoid R] 
{R' : Type u_2} [inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'),   MulChar.m
ulEquivToUnitHom χ = …
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
-/
theorem mulCharEquiv_symm_apply_apply (m : Mˣ) (χ : MulChar M R) :
    (mulCharEquiv M R).symm m χ = χ m := by
  classical
  rw [show ((mulCharEquiv M R).symm m) χ =
    if IsUnit χ then ↑(mulEquivToUnitHom χ m) else (0 : R) by rfl, if_pos (Group.isUnit χ),
    mulEquivToUnitHom_apply, coe_equivToUnitHom]

@[simp]
/-
**MulChar.apply_mulCharEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：apply_mulCharEquiv (χ : MulChar M R) (η : MulChar (MulChar M R) R) : χ (mu
lCharEquiv M R η) = η χ
参数：χ : MulChar M R；η : MulChar (MulChar M R) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulChar.mulCharEquiv_symm_apply_apply`：mulCharEquiv_symm_apply_apply (m 
: Mˣ) (χ : MulChar M R) : (mulCharEquiv M R).symm m χ = χ m
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem apply_mulCharEquiv (χ : MulChar M R) (η : MulChar (MulChar M R) R) :
    χ (mulCharEquiv M R η) = η χ := by
  rw [← mulCharEquiv_symm_apply_apply (mulCharEquiv M R η) χ, MulEquiv.symm_apply_apply]

variable (M R) in
/--
The order reversing bijection that sends a subgroup of `Mˣ` to its dual subgroup in
`MulChar M R` where `M` is a finite commutative monoid and `R` is a ring with enough
roots of unity.
-/
/-
**MulChar.subgroupOrderIsoSubgroupMulChar** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：subgroupOrderIsoSubgroupMulChar : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒ
ᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order reversing bijection that sends a subgroup of `Mˣ` to its dual subgroup
 in
`MulChar M R` where `M` is a finite commutative monoid and `R` is a ring with en
ough
roots of unity.
-/
noncomputable def subgroupOrderIsoSubgroupMulChar : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒᵈ :=
  (CommGroup.subgroupOrderIsoSubgroupMonoidHom Mˣ R).trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]
/-
**MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mul
Char`。
形式化陈述：mem_subgroupOrderIsoSubgroupMulChar_iff {H : Subgroup Mˣ} {χ : MulChar M R
} : χ in (subgroupOrderIsoSubgroupMulChar M R H).ofDual ↔ forall m in H, χ m = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.subgroupOrderIsoSubgroupMulChar.eq_1`：∀ (M : Type u_1) (R : Type
 u_2) [inst : CommMonoid M] [inst_1 : CommRing R] [inst_2 : Finite M]   [inst_3 
: HasEnoughRootsOfUnity R (Monoid.…
· 使用定理 `OrderIso.trans_apply`：trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e
.trans e' x = e' (e x)
· 使用定理 `OrderIso.dual_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (f : α ≃o β) (x : αᵒᵈ),   f.dual x = OrderDual.toDual (f (OrderDual.o
fDual x))
· 使用引理 `MulEquiv.coe_mapSubgroup`：coe_mapSubgroup (e : G ≃* H) : mapSubgroup e =
 Subgroup.map e.toMonoidHom
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
· 使用定理 `Subgroup.mem_map_equiv`：mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x :
 N} : x in K.map f.toMonoidHom ↔ f.symm x in K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.mulEquivToUnitHom_apply`：∀ {R : Type u_1} [inst : CommMonoid R] 
{R' : Type u_2} [inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'),   MulChar.m
ulEquivToUnitHom χ = …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subgroupOrderIsoSubgroupMulChar_iff {H : Subgroup Mˣ} {χ : MulChar M R} :
    χ ∈ (subgroupOrderIsoSubgroupMulChar M R H).ofDual ↔ ∀ m ∈ H, χ m = 1 := by
  rw [subgroupOrderIsoSubgroupMulChar, OrderIso.trans_apply, OrderIso.dual_apply,
    MulEquiv.coe_mapSubgroup, OrderDual.ofDual_toDual, Subgroup.mem_map_equiv]
  simp [← Units.val_eq_one]

@[simp]
/-
**MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MulChar`。
形式化陈述：mem_subgroupOrderIsoSubgroupMulChar_symm_iff {X : Subgroup (MulChar M R)} 
{m : Mˣ} : m in (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual X) 
↔ forall χ in X, χ m = 1
参数：MulChar M R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.mapSubgroup_apply`：∀ {G : Type u_1} [inst : Group G] {H : Type 
u_6} [inst_1 : Group H] (f : G ≃* H) (H_1 : Subgroup G),   f.mapSubgroup H_1 = S
ubgroup.map (↑f)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulChar.mulEquivToUnitHom_apply`：∀ {R : Type u_1} [inst : CommMonoid R] 
{R' : Type u_2} [inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'),   MulChar.m
ulEquivToUnitHom χ = …
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subgroupOrderIsoSubgroupMulChar_symm_iff {X : Subgroup (MulChar M R)} {m : Mˣ} :
    m ∈ (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual X) ↔ ∀ χ ∈ X, χ m = 1 := by
  simp [subgroupOrderIsoSubgroupMulChar, ← Units.val_eq_one]

/-- The cardinality of the dual subgroup of `MulChar M R` associated to a subgroup `H` of `Mˣ`
equals the index of `H` in `Mˣ`. -/
/-
**MulChar.card_subgroupOrderIsoSubgroupMulChar** 是 Mathlib 中的一个定理，位于命名空间 `MulCha
r`。
形式化陈述：card_subgroupOrderIsoSubgroupMulChar {H : Subgroup Mˣ} : Nat.card (subgrou
pOrderIsoSubgroupMulChar M R H).ofDual = Nat.card (Mˣ ⧸ H)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.subgroupOrderIsoSubgroupMulChar.eq_1`：∀ (M : Type u_1) (R : Type
 u_2) [inst : CommMonoid M] [inst_1 : CommRing R] [inst_2 : Finite M]   [inst_3 
: HasEnoughRootsOfUnity R (Monoid.…
· 使用定理 `OrderIso.trans_apply`：trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e
.trans e' x = e' (e x)
· 使用定理 `OrderIso.dual_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (f : α ≃o β) (x : αᵒᵈ),   f.dual x = OrderDual.toDual (f (OrderDual.o
fDual x))
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
· 使用定理 `Subgroup.card_mapSubgroup`：card_mapSubgroup {G' : Type*} [Group G'] (e :
 G ≃* G') : Nat.card (e.mapSubgroup H) = Nat.card H
· 使用定理 `CommGroup.card_subgroupOrderIsoSubgroupMonoidHom`：card_subgroupOrderIsoS
ubgroupMonoidHom (H : Subgroup G) : Nat.card (subgroupOrderIsoSubgroupMonoidHom 
G M H).ofDual = Nat.card (G ⧸ H)

--- 原说明 ---
The cardinality of the dual subgroup of `MulChar M R` associated to a subgroup `
H` of `Mˣ`
equals the index of `H` in `Mˣ`.
-/
theorem card_subgroupOrderIsoSubgroupMulChar {H : Subgroup Mˣ} :
    Nat.card (subgroupOrderIsoSubgroupMulChar M R H).ofDual = Nat.card (Mˣ ⧸ H) := by
  rw [subgroupOrderIsoSubgroupMulChar, OrderIso.trans_apply, OrderIso.dual_apply,
    OrderDual.ofDual_toDual, Subgroup.card_mapSubgroup,
    CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]

end MulChar

