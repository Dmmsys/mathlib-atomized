/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Transfer

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `Subgroup.exists_right_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `Subgroup.exists_left_complement'_of_coprime`: The **Schur-Zassenhaus** theorem:
  If `H : Subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/

@[expose] public section


namespace Subgroup

section SchurZassenhausAbelian

open MulOpposite MulAction Subgroup.leftTransversals
open scoped IsMulCommutative

variable {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] [FiniteIndex H]
  (α β : H.LeftTransversal)

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation. -/
/-
**Subgroup.QuotientDiff** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：QuotientDiff
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of the transversals of an abelian normal `N` by the `diff` relation
.
-/
def QuotientDiff :=
  Quotient
    (Setoid.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun h => by rw [← diff_inv, h, inv_one],
        fun h h' => by rw [← diff_mul_diff, h, h', one_mul]⟩)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited H.QuotientDiff :=
  inferInstanceAs (Inhabited <| Quotient _)
/-
**Subgroup.smul_diff_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) : diff (MonoidHom.id H) (g • α)
 (g • β) = ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop, hH.mem_comm ((c
ongr_arg (· in H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
参数：g : Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.mem_comm`：mem_comm (nH : H.Normal) {a b : G} (h : a * b 
in H) : b * a in H
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subgroup.coe_mk`：coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x
· 使用定理 `Subgroup.coe_one`：coe_one : ((1 : H) : G) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.smul_apply_eq_smul_apply_inv_smul`：smul_apply_eq_smul_apply_inv
_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) : ((f • S).2.leftQuotientEquiv
 q : G) = f • (S.2.leftQuotientE…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `MulAction.toPerm_symm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Gro
up α] [inst_1 : MulAction α β] (a : α) (x : β),   (Equiv.symm (MulAction.toPerm 
a)) x = a⁻¹ • x
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) :
    diff (MonoidHom.id H) (g • α) (g • β) =
      ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop,
        hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩ := by
  let := H.fintypeQuotientOfFiniteIndex
  let ϕ : H →* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop,
          hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩
      map_one' := by rw [Subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_cancel]
      map_mul' := fun h₁ h₂ => by
        simp only [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left] }
  refine (Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun x ↦ ?_).trans (map_prod ϕ _ _).symm
  simp only [ϕ, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, mul_inv_rev, mul_assoc,
    MonoidHom.id_apply, toPerm_symm_apply, MonoidHom.coe_mk, OneHom.coe_mk]

variable {H}
variable [Normal H]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MulAction G H.QuotientDiff where
  smul g :=
    Quotient.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_eq_left, ←
            coe_one, ← Subtype.ext_iff])
  mul_smul g₁ g₂ q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [mul_inv_rev]; exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)
  one_smul q :=
    Quotient.inductionOn' q fun T =>
      congr_arg Quotient.mk'' (by rw [inv_one]; apply one_smul Gᵐᵒᵖ T)
/-
**Subgroup.smul_diff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_diff' (h : H) : diff (MonoidHom.id H) α (op (h : G) • β) = diff (Mono
idHom.id H) α β * h ^ H.index
参数：h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.leftTransversals.diff.eq_1`：∀ {G : Type u_1} [inst : Group G] {
H : Subgroup G} {A : Type u_2} [inst_1 : CommGroup A] (ϕ : ↥H →* A)   (S T : H.L
eftTransversal) [inst_2 :…
· 使用定理 `Subgroup.index_eq_card`：index_eq_card : H.index = Nat.card (G ⧸ H)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.smul_apply_eq_smul_apply_inv_smul`：smul_apply_eq_smul_apply_inv
_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) : ((f • S).2.leftQuotientEquiv
 q : G) = f • (S.2.leftQuotientE…
· 使用引理 `MulOpposite.smul_eq_mul_unop`：MulOpposite.smul_eq_mul_unop [Mul α] (a : 
αᵐᵒᵖ) (b : α) : a • b = b * a.unop
· 使用定理 `MulOpposite.unop_op`：unop_op (x : α) : unop (op x) = x
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_eq_mul`：left_eq_mul : a = a * b ↔ b = 1
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
-/
theorem smul_diff' (h : H) :
    diff (MonoidHom.id H) α (op (h : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index := by
  let := H.fintypeQuotientOfFiniteIndex
  rw [diff, diff, index_eq_card, Nat.card_eq_fintype_card,
      ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul, mul_assoc, mul_right_inj]
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, MulOpposite.unop_op, mul_left_inj,
    ← Subtype.ext_iff, Equiv.apply_eq_iff_eq, inv_smul_eq_iff]
  exact left_eq_mul.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)
/-
**Subgroup.eq_one_of_smul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：eq_one_of_smul_eq_one (hH : Nat.Coprime (Nat.card H) H.index) (α : H.Quoti
entDiff) (h : H) : h • α = α -> h = 1
参数：hH : Nat.Coprime (Nat.card H) H.index；α : H.QuotientDiff；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.leftTransversals.diff_inv`：diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T
 S
· 使用定理 `Subgroup.smul_diff'`：smul_diff' (h : H) : diff (MonoidHom.id H) α (op (h
 : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index
· 使用定理 `Subgroup.leftTransversals.diff_self`：diff_self : diff ϕ T T = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem eq_one_of_smul_eq_one (hH : Nat.Coprime (Nat.card H) H.index) (α : H.QuotientDiff)
    (h : H) : h • α = α → h = 1 :=
  Quotient.inductionOn' α fun α hα =>
    (powCoprime hH).injective <|
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv, smul_diff', diff_self, one_mul, inv_pow, inv_inv]
        _ = 1 ^ H.index := (Quotient.exact' hα).trans (one_pow H.index).symm
/-
**Subgroup.exists_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：exists_smul_eq (hH : Nat.Coprime (Nat.card H) H.index) (α β : H.QuotientDi
ff) : exists h : H, h • α = β
参数：hH : Nat.Coprime (Nat.card H) H.index；α β : H.QuotientDiff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.leftTransversals.diff_inv`：diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T
 S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
· 使用定理 `Subgroup.smul_diff'`：smul_diff' (h : H) : diff (MonoidHom.id H) α (op (h
 : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `powCoprime_apply`：∀ {n : ℕ} {G : Type u_6} [inst : Group G] (h : (Nat.ca
rd G).Coprime n) (g : G), (powCoprime h) g = g ^ n
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem exists_smul_eq (hH : Nat.Coprime (Nat.card H) H.index) (α β : H.QuotientDiff) :
    ∃ h : H, h • α = β :=
  Quotient.inductionOn' α
    (Quotient.inductionOn' β fun β α =>
      Exists.imp (fun _ => Quotient.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidHom.id H) β α))⁻¹).trans
                (by rw [inv_pow, ← powCoprime_apply hH, Equiv.apply_symm_apply, mul_inv_cancel])))⟩)
/-
**Subgroup.isComplement'_stabilizer_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} [inst_1 : IsMulCommutat
ive ↥H] [inst_2 : H.FiniteIndex]   [inst_3 : H.Normal] {α : H.QuotientDiff}, (Na
t.card ↥H).Coprime H.index → H.IsComplement' (MulAction.stabilizer G α)
参数：Nat.card ↥H；MulAction.stabilizer G α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isComplement'_stabilizer`：∀ {G : Type u_1} [inst : Group G] {H 
: Subgroup G} {α : Type u_2} [inst_1 : MulAction G α] (a : α),   (∀ (h : ↥H), h 
• a = a → h = 1) → (∀ (…
· 使用定理 `Subgroup.eq_one_of_smul_eq_one`：eq_one_of_smul_eq_one (hH : Nat.Coprime 
(Nat.card H) H.index) (α : H.QuotientDiff) (h : H) : h • α = α -> h = 1
· 使用定理 `Subgroup.exists_smul_eq`：exists_smul_eq (hH : Nat.Coprime (Nat.card H) H
.index) (α β : H.QuotientDiff) : exists h : H, h • α = β
-/
theorem isComplement'_stabilizer_of_coprime {α : H.QuotientDiff}
    (hH : Nat.Coprime (Nat.card H) H.index) : IsComplement' H (stabilizer G α) :=
  isComplement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.exists_right_complement'_of_coprime_aux** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem exists_right_complement'_of_coprime_aux (hH : Nat.Coprime (Nat.card H) H.index) :
    ∃ K : Subgroup G, IsComplement' H K :=
  have ne : Nonempty (QuotientDiff H) := inferInstance
  ne.elim fun α => ⟨stabilizer G α, isComplement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Group G] {N : Subgroup G} [Normal N]
  (h1 : Nat.Coprime (Nat.card N) N.index)
  (h2 : ∀ (G' : Type u) [Group G'] [Finite G'],
    Nat.card G' < Nat.card G → ∀ {N' : Subgroup G'} [N'.Normal],
      Nat.Coprime (Nat.card N') N'.index → ∃ H' : Subgroup G', IsComplement' N' H')
  (h3 : ∀ H : Subgroup G, ¬IsComplement' N H)
include h1 h3

/-! We will arrive at a contradiction via the following steps:
* step 0: `N` (the normal Hall subgroup) is nontrivial.
* step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
* step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
* step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
* step 4: `p` (`min_fact (Fintype.card N)`) is prime (follows from step0).
* step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
* step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
* step 7: `N` is abelian (applies step 3 to the center of `N`).
-/


/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step0** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step0 : N ≠ ⊥ := by
  rintro rfl
  exact h3 ⊤ isComplement'_bot_top

variable [Finite G]

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step1** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step1 (K : Subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ := by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relIndex_top_right, ← hK]
    exact (relIndex_sup_right K N).symm
  have h5 : Nat.card K < Nat.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.Coprime (Nat.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  replace hH : Nat.card (H.map K.subtype) = N.index := by
    rw [← relIndex_bot_left, ← relIndex_comap, MonoidHom.comap_bot, Subgroup.ker_subtype,
      relIndex_bot_left, ← IsComplement'.index_eq_card (IsComplement'.symm hH), index_comap,
      range_subtype, ← relIndex_sup_right, hK, relIndex_top_right]
  have h7 : Nat.card N * Nat.card (H.map K.subtype) = Nat.card G := by
    rw [hH, ← N.index_mul_card, mul_comm]
  have h8 : (Nat.card N).Coprime (Nat.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, isComplement'_of_coprime h7 h8⟩

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step2** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K ≤ N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotient.mk''_surjective
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Nat.card (G ⧸ K) < Nat.card G := by
    rw [← index_eq_card, ← K.index_mul_card]
    refine
      lt_mul_of_one_lt_right (Nat.pos_of_ne_zero index_ne_zero_of_finite)
        (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 :
    (Nat.card (N.map (QuotientGroup.mk' K))).Coprime (N.map (QuotientGroup.mk' K)).index := by
    have index_map := N.index_map_eq this (by rwa [QuotientGroup.ker_mk'])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    rw [index_map]
    refine h1.coprime_dvd_left ?_
    rw [← Nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ← index_map, index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  refine ⟨H.comap (QuotientGroup.mk' K), ?_, ?_⟩
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine comap_map_eq_self ?_
      rwa [QuotientGroup.ker_mk']
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
  · rw [← comap_top (QuotientGroup.mk' K)]
    intro hH'
    rw [comap_injective this hH', isComplement'_top_right, map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hH
    exact h4.2 (le_antisymm hK hH)

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step3** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step3 (K : Subgroup N) [(K.map N.subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) (map_subtype_le K)
  rw [← map_bot N.subtype] at key
  conv at key =>
    rhs
    rhs
    rw [← N.range_subtype, N.subtype.range_eq_map]
  rwa [map_subtype_inj, map_subtype_inj] at key

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step4** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step4 : (Nat.card N).minFac.Prime :=
  Nat.minFac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h3)).ne'

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step5** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step5 {P : Sylow (Nat.card N).minFac N} : P.1 ≠ ⊥ := by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  apply P.ne_bot_of_dvd_card
  exact (Nat.card N).minFac_dvd

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step6** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem step6 : IsPGroup (Nat.card N).minFac N := by
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  refine Sylow.nonempty.elim fun P => P.2.of_surjective P.1.subtype ?_
  rw [← MonoidHom.range_eq_top, range_subtype]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top_iff.mp (step1 h1 h2 h3 _ P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h3)

include h2 in
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.SchurZassenhausInduction.step7** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Sc
hurZassenhausInduction`。
形式化陈述：step7 : IsMulCommutative N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Subgroup.bot_or_nontrivial`：bot_or_nontrivial (H : Subgroup G) : H = ⊥ ∨
 Nontrivial H
· 使用定理 `_private.Mathlib.GroupTheory.SchurZassenhaus.0.Subgroup.SchurZassenhausI
nduction.step0`：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal],   (
Nat.card ↥N).Coprime N.index → (∀ (H : Subgroup G), ¬N.IsComplement' H) → N …
· 使用定理 `_private.Mathlib.GroupTheory.SchurZassenhaus.0.Subgroup.SchurZassenhausI
nduction.step4`：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal],   (
Nat.card ↥N).Coprime N.index →     (∀ (H : Subgroup G), ¬N.IsComplement' H) …
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `_private.Mathlib.GroupTheory.SchurZassenhaus.0.Subgroup.SchurZassenhausI
nduction.step3`：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal],   (
Nat.card ↥N).Coprime N.index →     (∀ (G' : Type u) [inst : Group G'] [Finit…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsPGroup.bot_lt_center`：bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Su
bgroup.center G
· 使用定理 `_private.Mathlib.GroupTheory.SchurZassenhaus.0.Subgroup.SchurZassenhausI
nduction.step6`：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal],   (
Nat.card ↥N).Coprime N.index →     (∀ (G' : Type u) [inst : Group G'] [Finit…
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
theorem step7 : IsMulCommutative N := by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h3)
  have : Fact (Nat.card N).minFac.Prime := ⟨step4 h1 h3⟩
  exact
    ⟨⟨fun g h => ((eq_top_iff.mp ((step3 h1 h2 h3 (center N)).resolve_left
      (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h)).comm g).symm⟩⟩

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Group G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
/-
**Subgroup.exists_right_complement'_of_coprime_aux'** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do not use this lemma: It is made obsolete by `exists_right_complement'_of_copri
me`
-/
private theorem exists_right_complement'_of_coprime_aux' [Finite G] (hG : Nat.card G = n)
    {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' N H := by
  revert G
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rintro G _ _ rfl N _ hN
  refine not_forall_not.mp fun h3 => ?_
  have := SchurZassenhausInduction.step7 hN (fun G' _ _ hG' => by apply ih _ hG'; rfl) h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
/-
**Subgroup.exists_right_complement'_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal], (Nat.card ↥N)
.Coprime N.index → ∃ H, N.IsComplement' H
参数：Nat.card ↥N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `Subgroup.isComplement'_top_bot`：∀ {G : Type u_1} [inst : Group G], ⊤.IsC
omplement' ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥
· 使用定理 `Subgroup.isComplement'_bot_top`：∀ {G : Type u_1} [inst : Group G], ⊥.IsC
omplement' ⊤
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `_private.Mathlib.GroupTheory.SchurZassenhaus.0.Subgroup.exists_right_com
plement'_of_coprime_aux'`：∀ {n : ℕ} {G : Type u} [inst : Group G] [Finite G],   
Nat.card G = n → ∀ {N : Subgroup G} [N.Normal], (Nat.card ↥N).Coprime N.index → 
∃ H, N…

--- 原说明 ---
**Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there 
exists a
  subgroup `K` which is a (right) complement of `H`.
-/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H := by
  by_cases hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_left, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, isComplement'_top_bot⟩
  by_cases hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_right, Nat.card_eq_one_iff_unique] at hN
    have := hN.1
    rw [N.eq_bot_of_subsingleton]
    exact ⟨⊤, isComplement'_bot_top⟩
  have hN3 : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  exact exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
/-
**Subgroup.exists_left_complement'_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：∀ {G : Type u} [inst : Group G] {N : Subgroup G} [N.Normal], (Nat.card ↥N)
.Coprime N.index → ∃ H, H.IsComplement' N
参数：Nat.card ↥N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subgroup.IsComplement'.symm`：∀ {G : Type u_1} [inst : Group G] {H K : Su
bgroup G}, H.IsComplement' K → K.IsComplement' H
· 使用定理 `Subgroup.exists_right_complement'_of_coprime`：∀ {G : Type u} [inst : Gro
up G] {N : Subgroup G} [N.Normal], (Nat.card ↥N).Coprime N.index → ∃ H, N.IsComp
lement' H

--- 原说明 ---
**Schur-Zassenhaus** for normal subgroups:
  If `H : Subgroup G` is normal, and has order coprime to its index, then there 
exists a
  subgroup `K` which is a (left) complement of `H`.
-/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup

