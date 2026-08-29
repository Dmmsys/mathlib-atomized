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

/--
lemma `dvd_exponent` / 引理 `dvd_exponent`

English:
lemma dvd_exponent
  statement: {ι G : Type*} [Monoid G] {n : ι -> Nat}
  proof: by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

中文:
引理 dvd_exponent
  结论: {ι G : 类型} [幺半群 G] {n : ι -> 自然数}
  证明: by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _
-/
private lemma dvd_exponent {ι G : Type*} [Monoid G] {n : ι -> Nat}
    (e : G ≃* ((i : ι) -> Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent G := by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

variable (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]

private
/--
lemma `exists_apply_ne_one_aux` / 引理 `exists_apply_ne_one_aux`

English:
lemma exists_apply_ne_one_aux
  proof: by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let e := h.some
  obtain ⟨i, hi⟩ : exists i : ι, e a i != 1 := by
    contrapose! ha
exact (MulEquiv.map_eq_one_iff e).mp funext ha
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) ((e a i).toAdd) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) => Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using! hφi

中文:
引理 存在_apply_ne_one_aux
  证明: by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let e := h.some
  obtain ⟨i, hi⟩ : exists i : ι, e a i != 1 := by
    contrapose! ha
exact (MulEquiv.map_eq_one_iff e).mp funext ha
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) ((e a i).toAdd) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) => Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using! hφi

Depends on / 依赖: CommGroup, CommGroup.equiv_prod_multiplicative_zmod_of_finite, Function, Function.comp_apply, MulEquiv, MulEquiv.map_eq_one_iff, Multiplicative, Pi.evalMonoidHom, Pi.evalMonoidHom_apply, coe_coe, coe_comp, comp_apply, contrapose, dvd_exponent, equiv_prod_multiplicative_zmod_of_finite, evalMonoidHom, evalMonoidHom_apply, h.some, i.comp, map_eq_one_iff
-/
lemma exists_apply_ne_one_aux
    (H : forall n : Nat, n ∣ Monoid.exponent G -> forall a : ZMod n, a != 0 ->
      exists φ : Multiplicative (ZMod n) ->* M, φ (.ofAdd a) != 1)
    {a : G} (ha : a != 1) :
    exists φ : G ->* M, φ a != 1 := by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let e := h.some
  obtain ⟨i, hi⟩ : exists i : ι, e a i != 1 := by
    contrapose! ha
exact (MulEquiv.map_eq_one_iff e).mp funext ha
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) ((e a i).toAdd) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) => Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using! hφi

variable [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

/--
theorem `exists_apply_ne_one_of_hasEnoughRootsOfUnity` / 定理 `exists_apply_ne_one_of_hasEnoughRootsOfUnity`

English:
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity
  given: {a : G} (ha : a != 1)
  proof: by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ => ?_) ha
have : NeZero n := ⟨fun H => NeZero.ne _ Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

中文:
定理 存在_apply_ne_one_of_hasEnoughRootsOfUnity
  条件: {a : G} (ha : a != 1)
  证明: by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ => ?_) ha
have : NeZero n := ⟨fun H => NeZero.ne _ Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.exists_primitiveRoot, HasEnoughRootsOfUnity.of_dvd, Nat.eq_zero_of_zero_dvd, NeZero, NeZero.ne, ZMod.exists_monoidHom_apply_ne_one, eq_zero_of_zero_dvd, exists_apply_ne_one_aux, exists_monoidHom_apply_ne_one, exists_primitiveRoot, of_dvd
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity {a : G} (ha : a != 1) :
    exists φ : G ->* Mˣ, φ a != 1 := by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ => ?_) ha
have : NeZero n := ⟨fun H => NeZero.ne _ Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

variable {M} in
@[simp]
/--
theorem `forall_apply_eq_apply_iff` / 定理 `forall_apply_eq_apply_iff`

English:
theorem forall_apply_eq_apply_iff
  given: {g g' : G}
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simpa [← not_forall, not_imp_not, mul_inv_eq_one, h] using
    exists_apply_ne_one_of_hasEnoughRootsOfUnity G M (a := g * g'⁻¹)

中文:
定理 对任意_apply_eq_apply_iff
  条件: {g g' : G}
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simpa [← not_forall, not_imp_not, mul_inv_eq_one, h] using
    exists_apply_ne_one_of_hasEnoughRootsOfUnity G M (a := g * g'⁻¹)

Depends on / 依赖: exists_apply_ne_one_of_hasEnoughRootsOfUnity, mul_inv_eq_one, not_forall, not_imp_not
-/
theorem forall_apply_eq_apply_iff {g g' : G} :
    (forall φ : G ->* Mˣ, φ g = φ g') ↔ g = g' := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simpa [← not_forall, not_imp_not, mul_inv_eq_one, h] using
    exists_apply_ne_one_of_hasEnoughRootsOfUnity G M (a := g * g'⁻¹)

/--
theorem `monoidHom_mulEquiv_of_hasEnoughRootsOfUnity` / 定理 `monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`

English:
theorem monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
  statement: Nonempty ((G ->* Mˣ) ≃* G)
  proof: by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i => Multiplicative (ZMod (n i))) Mˣ
  have : forall i, NeZero (n i) := fun i => NeZero.of_gt (h₁ i)
have inst i : HasEnoughRootsOfUnity M Nat.card Multiplicative ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
exact ⟨e.monoidHomCongrLeft.trans e'.trans .trans (.piCongrRight E) e.symm⟩

中文:
定理 monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
  结论: 非空 ((G ->* Mˣ) ≃* G)
  证明: by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i => Multiplicative (ZMod (n i))) Mˣ
  have : forall i, NeZero (n i) := fun i => NeZero.of_gt (h₁ i)
have inst i : HasEnoughRootsOfUnity M Nat.card Multiplicative ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
exact ⟨e.monoidHomCongrLeft.trans e'.trans .trans (.piCongrRight E) e.symm⟩

Depends on / 依赖: DecidableEq, Fintype, Fintype.card_multiplicative, HasEnoughRootsOfUnity, Monoid, Monoid.exponent, Multiplicative, Nat.card, Nat.card_eq_fintype_card, NeZero, NeZero.of_gt, Pi.monoidHomMulEquiv, ZMod.card, card_eq_fintype_card, card_multiplicative, classical, equiv_prod_multiplicative_zmod_of_finite, exponent, monoidHomMulEquiv, of_gt
-/
theorem monoidHom_mulEquiv_of_hasEnoughRootsOfUnity : Nonempty ((G ->* Mˣ) ≃* G) := by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i => Multiplicative (ZMod (n i))) Mˣ
  have : forall i, NeZero (n i) := fun i => NeZero.of_gt (h₁ i)
have inst i : HasEnoughRootsOfUnity M Nat.card Multiplicative ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
exact ⟨e.monoidHomCongrLeft.trans e'.trans .trans (.piCongrRight E) e.symm⟩

/--
theorem `card_monoidHom_of_hasEnoughRootsOfUnity` / 定理 `card_monoidHom_of_hasEnoughRootsOfUnity`

English:
theorem card_monoidHom_of_hasEnoughRootsOfUnity
  proof: Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

中文:
定理 card_monoidHom_of_hasEnoughRootsOfUnity
  证明: Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

Depends on / 依赖: Nat.card_congr, card_congr, monoidHom_mulEquiv_of_hasEnoughRootsOfUnity, some.toEquiv, toEquiv
-/
theorem card_monoidHom_of_hasEnoughRootsOfUnity :
    Nat.card (G ->* Mˣ) = Nat.card G :=
  Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

variable {G}

/--
theorem `_root_.MonoidHom.domRestrict_surjective` / 定理 `_root_.MonoidHom.domRestrict_surjective`

English:
theorem _root_.MonoidHom.domRestrict_surjective
  given: (H : Subgroup G)
  proof: by
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
hM.of_dvd M Monoid.exponent_submonoid_dvd H.toSubmonoid
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [H.card_eq_card_quotient_mul_card_subgroup]; rw [mul_div_cancel_right₀ _ (Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero)]; rw [← card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) M]; rw [Nat.card_congr (domRestrictHomKerEquiv Mˣ H).toEquiv]

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrict_surjective := _root_.MonoidHom.domRestrict_surjective

@[simp]

中文:
定理 _root_.幺半群态射.domRestrict_surjective
  条件: (H : 子群 G)
  证明: by
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
hM.of_dvd M Monoid.exponent_submonoid_dvd H.toSubmonoid
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [H.card_eq_card_quotient_mul_card_subgroup]; rw [mul_div_cancel_right₀ _ (Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero)]; rw [← card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) M]; rw [Nat.card_congr (domRestrictHomKerEquiv Mˣ H).toEquiv]

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrict_surjective := _root_.MonoidHom.domRestrict_surjective

@[simp]

Depends on / 依赖: Fintype, Fintype.card_e, Fintype.ofFinite, Group.exponent_quotient_dvd, H.card_eq_card_quotient_mul_card_subgroup, H.toSubmonoid, HasEnoughRootsOfUnity, Monoid, Monoid.exponent, Monoid.exponent_submonoid_dvd, MonoidHom, MonoidHom.surjective_of_card_ker_le_div, card_e, card_eq_card_quotient_mul_card_subgroup, card_monoidHom_of_hasEnoughRootsOfUnity, exponent, exponent_quotient_dvd, exponent_submonoid_dvd, hM.of_dvd, le_of_eq
-/
theorem _root_.MonoidHom.domRestrict_surjective (H : Subgroup G) :
    Function.Surjective (MonoidHom.domRestrictHom H Mˣ) := by
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
hM.of_dvd M Monoid.exponent_submonoid_dvd H.toSubmonoid
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]; rw [H.card_eq_card_quotient_mul_card_subgroup]; rw [mul_div_cancel_right₀ _ (Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero)]; rw [← card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) M]; rw [Nat.card_congr (domRestrictHomKerEquiv Mˣ H).toEquiv]

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrict_surjective := _root_.MonoidHom.domRestrict_surjective

@[simp]
/--
theorem `forall_monoidHom_apply_eq_one_iff` / 定理 `forall_monoidHom_apply_eq_one_iff`

English:
theorem forall_monoidHom_apply_eq_one_iff
  given: (H : Subgroup G) (x : G)
  proof: by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine ⟨fun h => ?_, fun hx φ hφ => hφ x hx⟩
  simp only [← QuotientGroup.eq_one_iff, ← forall_apply_eq_apply_iff _ (M := M), map_one] at h ⊢
  exact fun φ => h (φ.comp (QuotientGroup.mk' H)) fun y hy => hy φ

中文:
定理 对任意_monoidHom_apply_eq_one_iff
  条件: (H : 子群 G) (x : G)
  证明: by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine ⟨fun h => ?_, fun hx φ hφ => hφ x hx⟩
  simp only [← QuotientGroup.eq_one_iff, ← forall_apply_eq_apply_iff _ (M := M), map_one] at h ⊢
  exact fun φ => h (φ.comp (QuotientGroup.mk' H)) fun y hy => hy φ

Depends on / 依赖: Group.exponent_quotient_dvd, HasEnoughRootsOfUnity, Monoid, Monoid.exponent, QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.mk, eq_one_iff, exponent, exponent_quotient_dvd, forall_apply_eq_apply_iff, hM.of_dvd, map_one, of_dvd
-/
theorem forall_monoidHom_apply_eq_one_iff (H : Subgroup G) (x : G) :
    (forall (φ : G ->* Mˣ), (forall y in H, φ y = 1) -> φ x = 1) ↔ x in H := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  refine ⟨fun h => ?_, fun hx φ hφ => hφ x hx⟩
  simp only [← QuotientGroup.eq_one_iff, ← forall_apply_eq_apply_iff _ (M := M), map_one] at h ⊢
  exact fun φ => h (φ.comp (QuotientGroup.mk' H)) fun y hy => hy φ

/--
theorem `card_domRestrictHom_ker` / 定理 `card_domRestrictHom_ker`

English:
theorem card_domRestrictHom_ker
  given: (H : Subgroup G)
  proof: by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  rw [Nat.card_congr (MonoidHom.domRestrictHomKerEquiv Mˣ H).toEquiv]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]

@[deprecated (since := "2026-07-19")] alias card_restrictHom_ker := card_domRestrictHom_ker

中文:
定理 card_domRestrictHom_ker
  条件: (H : 子群 G)
  证明: by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  rw [Nat.card_congr (MonoidHom.domRestrictHomKerEquiv Mˣ H).toEquiv]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]

@[deprecated (since := "2026-07-19")] alias card_restrictHom_ker := card_domRestrictHom_ker

Depends on / 依赖: Group.exponent_quotient_dvd, HasEnoughRootsOfUnity, Monoid, Monoid.exponent, MonoidHom, MonoidHom.domRestrictHomKerEquiv, Nat.card_congr, card_congr, card_monoidHom_of_hasEnoughRootsOfUnity, domRestrictHomKerEquiv, exponent, exponent_quotient_dvd, hM.of_dvd, of_dvd, toEquiv
-/
theorem card_domRestrictHom_ker (H : Subgroup G) :
    Nat.card (domRestrictHom H Mˣ).ker = Nat.card (G ⧸ H) := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
hM.of_dvd M Group.exponent_quotient_dvd H
  rw [Nat.card_congr (MonoidHom.domRestrictHomKerEquiv Mˣ H).toEquiv]; rw [card_monoidHom_of_hasEnoughRootsOfUnity]

@[deprecated (since := "2026-07-19")] alias card_restrictHom_ker := card_domRestrictHom_ker

variable (G) in
/--
The `MulEquiv` between the double dual `(G →* Mˣ) →* Mˣ` of a finite commutative group `G`
and itself where `M` is a commutative monoid with enough `n`th roots of unity, where `n` is
the exponent of `G`.
The image `g` of `η : (G →* Mˣ) →* Mˣ` is such that, for all `φ : G →* Mˣ`, we have `φ g = η g`,
see `CommGroup.apply_monoidHomMonoidHomEquiv`.
-/
@[simps! symm_apply_apply]
/--
Definition of `monoidHomMonoidHomEquiv` / `monoidHomMonoidHomEquiv` 的定义

English:
definition monoidHomMonoidHomEquiv
  signature: :
  body: have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g => MonoidHom.mk ⟨fun φ => φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h => ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity]))
    (fun _ _ => by ext; simp)).symm

@[simp]

中文:
定义 monoidHomMonoidHomEquiv
  签名: :
  定义体: have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g => MonoidHom.mk ⟨fun φ => φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h => ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity]))
    (fun _ _ => by ext; simp)).symm

@[simp]

Depends on / 依赖: Equiv.ofBijective, HasEnoughRootsOfUnity, Monoid, Monoid.exponent, Monoid.exponent_eq_of_mulEquiv, MonoidHom, MonoidHom.mk, MulEquiv, MulEquiv.mk, Nat.bijective_iff_injective_and_card, OneHom, OneHom.mk.injEq, bijective_iff_injective_and_card, card_monoidHom_of_hasEnoughRootsOfUnity, exponent, exponent_eq_of_mulEquiv, forall_apply_eq_apply_iff, funext_iff, mk.injEq, monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
-/
noncomputable def monoidHomMonoidHomEquiv :
    ((G ->* Mˣ) ->* Mˣ) ≃* G :=
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g => MonoidHom.mk ⟨fun φ => φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h => ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity]))
    (fun _ _ => by ext; simp)).symm

@[simp]
/--
theorem `apply_monoidHomMonoidHomEquiv` / 定理 `apply_monoidHomMonoidHomEquiv`

English:
theorem apply_monoidHomMonoidHomEquiv
  given: (φ : G ->* Mˣ) (η : (G ->* Mˣ) ->* Mˣ)
  proof: by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G M (monoidHomMonoidHomEquiv G M η) φ]; rw [MulEquiv.symm_apply_apply]

中文:
定理 apply_monoidHomMonoidHomEquiv
  条件: (φ : G ->* Mˣ) (η : (G ->* Mˣ) ->* Mˣ)
  证明: by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G M (monoidHomMonoidHomEquiv G M η) φ]; rw [MulEquiv.symm_apply_apply]

Depends on / 依赖: MulEquiv, MulEquiv.symm_apply_apply, monoidHomMonoidHomEquiv, monoidHomMonoidHomEquiv_symm_apply_apply, symm_apply_apply
-/
theorem apply_monoidHomMonoidHomEquiv (φ : G ->* Mˣ) (η : (G ->* Mˣ) ->* Mˣ) :
    φ (monoidHomMonoidHomEquiv G M η) = η φ := by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G M (monoidHomMonoidHomEquiv G M η) φ]; rw [MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
variable (G) in
/--
Definition of `subgroupOrderIsoSubgroupMonoidHom` / `subgroupOrderIsoSubgroupMonoidHom` 的定义

English:
definition subgroupOrderIsoSubgroupMonoidHom
  signature: : Subgroup G ≃o (Subgroup (G ->* Mˣ))ᵒᵈ where
  body: OrderDual.toDual (domRestrictHom H Mˣ).ker
  invFun Φ := (monoidHomMonoidHomEquiv G M).mapSubgroup (domRestrictHom Φ.ofDual Mˣ).ker
  map_rel_iff' {H₁} {H₂} := by
    simp_rw [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual,
      SetLike.le_def, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff]
    grind [forall_monoidHom_apply_eq_one_iff M H₂]
  left_inv H := by
    ext x
    rw [MulEquiv.coe_mapSubgroup]; rw [Subgroup.mem_map_equiv]; rw [MonoidHom.mem_ker]
    simp
  right_inv Φ := by
    have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
      rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
    ext φ
    rw [OrderDual.ofDual_toDual]; rw [mem_ker]; rw [domRestrictHom_apply]; rw [domRestrict_eq_one_iff]
    simp

@[simp]

中文:
定义 subgroupOrderIsoSubgroupMonoidHom
  签名: : 子群 G ≃o (子群 (G ->* Mˣ))ᵒᵈ where
  定义体: OrderDual.toDual (domRestrictHom H Mˣ).ker
  invFun Φ := (monoidHomMonoidHomEquiv G M).mapSubgroup (domRestrictHom Φ.ofDual Mˣ).ker
  map_rel_iff' {H₁} {H₂} := by
    simp_rw [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual,
      SetLike.le_def, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff]
    grind [forall_monoidHom_apply_eq_one_iff M H₂]
  left_inv H := by
    ext x
    rw [MulEquiv.coe_mapSubgroup]; rw [Subgroup.mem_map_equiv]; rw [MonoidHom.mem_ker]
    simp
  right_inv Φ := by
    have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
      rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
    ext φ
    rw [OrderDual.ofDual_toDual]; rw [mem_ker]; rw [domRestrictHom_apply]; rw [domRestrict_eq_one_iff]
    simp

@[simp]

Depends on / 依赖: OrderDual, OrderDual.toDual, domRestrictHom, toDual
-/
noncomputable def subgroupOrderIsoSubgroupMonoidHom : Subgroup G ≃o (Subgroup (G ->* Mˣ))ᵒᵈ where
  toFun H := OrderDual.toDual (domRestrictHom H Mˣ).ker
  invFun Φ := (monoidHomMonoidHomEquiv G M).mapSubgroup (domRestrictHom Φ.ofDual Mˣ).ker
  map_rel_iff' {H₁} {H₂} := by
    simp_rw [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual,
      SetLike.le_def, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff]
    grind [forall_monoidHom_apply_eq_one_iff M H₂]
  left_inv H := by
    ext x
    rw [MulEquiv.coe_mapSubgroup]; rw [Subgroup.mem_map_equiv]; rw [MonoidHom.mem_ker]
    simp
  right_inv Φ := by
    have : HasEnoughRootsOfUnity M (Monoid.exponent (G ->* Mˣ)) := by
      rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some]
    ext φ
    rw [OrderDual.ofDual_toDual]; rw [mem_ker]; rw [domRestrictHom_apply]; rw [domRestrict_eq_one_iff]
    simp

@[simp]
/--
theorem `mem_subgroupOrderIsoSubgroupMonoidHom_iff` / 定理 `mem_subgroupOrderIsoSubgroupMonoidHom_iff`

English:
theorem mem_subgroupOrderIsoSubgroupMonoidHom_iff
  given: (H : Subgroup G) (φ : G ->* Mˣ)
  proof: by
  simp [subgroupOrderIsoSubgroupMonoidHom]

中文:
定理 mem_subgroupOrderIsoSubgroupMonoidHom_iff
  条件: (H : 子群 G) (φ : G ->* Mˣ)
  证明: by
  simp [subgroupOrderIsoSubgroupMonoidHom]

Depends on / 依赖: subgroupOrderIsoSubgroupMonoidHom
-/
theorem mem_subgroupOrderIsoSubgroupMonoidHom_iff (H : Subgroup G) (φ : G ->* Mˣ) :
    φ in (subgroupOrderIsoSubgroupMonoidHom G M H).ofDual ↔ forall g in H, φ g = 1 := by
  simp [subgroupOrderIsoSubgroupMonoidHom]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff` / 定理 `mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff`

English:
theorem mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff
  given: (Φ : Subgroup (G ->* Mˣ)) (g : G)
  proof: by
  simp_rw [subgroupOrderIsoSubgroupMonoidHom, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff,
    monoidHomMonoidHomEquiv_symm_apply_apply]

中文:
定理 mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff
  条件: (Φ : 子群 (G ->* Mˣ)) (g : G)
  证明: by
  simp_rw [subgroupOrderIsoSubgroupMonoidHom, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff,
    monoidHomMonoidHomEquiv_symm_apply_apply]

Depends on / 依赖: Equiv.coe_fn_symm_mk, MulEquiv, MulEquiv.coe_mapSubgroup, OrderDual, OrderDual.ofDual_toDual, OrderIso, OrderIso.symm_mk, RelIso, RelIso.coe_fn_mk, Subgroup, Subgroup.mem_map_equiv, coe_fn_mk, coe_fn_symm_mk, coe_mapSubgroup, domRestrictHom_apply, domRestrict_eq_one_iff, mem_ker, mem_map_equiv, monoidHomMonoidHomEquiv_symm_apply_apply, ofDual_toDual
-/
theorem mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff (Φ : Subgroup (G ->* Mˣ)) (g : G) :
    g in (subgroupOrderIsoSubgroupMonoidHom G M).symm (OrderDual.toDual Φ) ↔ forall φ in Φ, φ g = 1 := by
  simp_rw [subgroupOrderIsoSubgroupMonoidHom, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff,
    monoidHomMonoidHomEquiv_symm_apply_apply]

/--
theorem `card_subgroupOrderIsoSubgroupMonoidHom` / 定理 `card_subgroupOrderIsoSubgroupMonoidHom`

English:
theorem card_subgroupOrderIsoSubgroupMonoidHom
  given: (H : Subgroup G)
  proof: card_domRestrictHom_ker _ _

中文:
定理 card_subgroupOrderIsoSubgroupMonoidHom
  条件: (H : 子群 G)
  证明: card_domRestrictHom_ker _ _

Depends on / 依赖: card_domRestrictHom_ker
-/
theorem card_subgroupOrderIsoSubgroupMonoidHom (H : Subgroup G) :
    Nat.card (subgroupOrderIsoSubgroupMonoidHom G M H).ofDual = Nat.card (G ⧸ H) :=
  card_domRestrictHom_ker _ _

end CommGroup
