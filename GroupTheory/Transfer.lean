/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transferCenterPow`: The transfer homomorphism `G →* center G`.

## Main results
- `transferCenterPow_apply`:
  The transfer homomorphism `G →* center G` is given by `g ↦ g ^ (center G).index`.
- `ker_transferSylow_isComplement'`: Burnside's transfer (or normal `p`-complement) theorem:
  If `hP : N(P) ≤ C(P)`, then `(transfer P hP).ker` is a normal `p`-complement.
-/

@[expose] public noncomputable section


variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H →* A)

namespace Subgroup

namespace leftTransversals

open Finset MulAction

open scoped Pointwise

variable (R S T : H.LeftTransversal) [FiniteIndex H]

/-- The difference of two left transversals -/
@[to_additive /-- The difference of two left transversals -/]
/-
**Subgroup.leftTransversals.diff** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.leftTransve
rsals`。
形式化陈述：diff : A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two left transversals
-/
def diff : A :=
  let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let _ := H.fintypeQuotientOfFiniteIndex
  ∏ q : G ⧸ H, ϕ
      ⟨(α q : G)⁻¹ * β q,
        QuotientGroup.leftRel_apply.mp <|
          Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]
/-
**Subgroup.leftTransversals.diff_mul_diff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.le
ftTransversals`。
形式化陈述：diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q _ =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by simp_rw [Subtype.ext_iff, coe_mul, mul_assoc, mul_inv_cancel_left])))

@[to_additive]
/-
**Subgroup.leftTransversals.diff_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.leftTr
ansversals`。
形式化陈述：diff_self : diff ϕ T T = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Subgroup.leftTransversals.diff_mul_diff`：diff_mul_diff : diff ϕ R S * di
ff ϕ S T = diff ϕ R T
-/
theorem diff_self : diff ϕ T T = 1 :=
  mul_eq_left.mp (diff_mul_diff ϕ T T T)

@[to_additive]
/-
**Subgroup.leftTransversals.diff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.leftTra
nsversals`。
形式化陈述：diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.leftTransversals.diff_mul_diff`：diff_mul_diff : diff ϕ R S * di
ff ϕ S T = diff ϕ R T
· 使用定理 `Subgroup.leftTransversals.diff_self`：diff_self : diff ϕ T T = 1
-/
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
  inv_eq_of_mul_eq_one_right <| (diff_mul_diff ϕ S T S).trans <| diff_self ϕ S

@[to_additive]
/-
**Subgroup.leftTransversals.smul_diff_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.l
eftTransversals`。
形式化陈述：smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.smul_apply_eq_smul_apply_inv_smul`：smul_apply_eq_smul_apply_inv
_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) : ((f • S).2.leftQuotientEquiv
 q : G) = f • (S.2.leftQuotientE…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `MulAction.toPerm_symm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Gro
up α] [inst_1 : MulAction α β] (a : α) (x : β),   (Equiv.symm (MulAction.toPerm 
a)) x = a⁻¹ • x
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  let _ := H.fintypeQuotientOfFiniteIndex
  Fintype.prod_equiv (MulAction.toPerm g).symm _ _ fun _ ↦ by
    simp only [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, toPerm_symm_apply]

end leftTransversals

open Equiv Function MulAction ZMod

variable (g : G)

variable (H) in
/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
/-
**Subgroup.transferFunction** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：transferFunction : G ⧸ H -> G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g 
^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choi
ce of
  representative `g₀` of `q₀`.
-/
def transferFunction : G ⧸ H → G := fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out.out
/-
**Subgroup.transferFunction_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：transferFunction_apply (q : G ⧸ H) : transferFunction H g q = g ^ (cast (q
uotientEquivSigmaZMod H g q).2 : Int) * (quotientEquivSigmaZMod H g q).1.out.out
参数：q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transferFunction_apply (q : G ⧸ H) :
    transferFunction H g q =
      g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) *
        (quotientEquivSigmaZMod H g q).1.out.out := rfl
/-
**Subgroup.coe_transferFunction** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q
参数：q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.transferFunction_apply`：transferFunction_apply (q : G ⧸ H) : tr
ansferFunction H g q = g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quot
ientEquivSigmaZMod H …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MulAction.Quotient.coe_smul_out`：∀ {G : Type u} {X : Type v} [inst : Gro
up G] [inst_1 : Monoid X] [inst_2 : MulAction X G] (H : Subgroup G)   [inst_3 : 
MulAction.QuotientAct…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Subgroup.quotientEquivSigmaZMod_symm_apply`：quotientEquivSigmaZMod_symm_
apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ZMod (minimalPeriod (g • 
·) q.out)) : (quotientEquivSigma…
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transferFunction_apply, ← smul_eq_mul, Quotient.coe_smul_out,
    ← quotientEquivSigmaZMod_symm_apply, Sigma.eta, symm_apply_apply]

variable (H) in
/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
/-
**Subgroup.transferSet** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：transferSet : Set G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` fo
r fixed choices
of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits
 in `G ⧸ H`.
-/
def transferSet : Set G := Set.range (transferFunction H g)
/-
**Subgroup.mem_transferSet** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_transferSet (q : G ⧸ H) : transferFunction H g q in transferSet H g
参数：q : G ⧸ H。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_transferSet (q : G ⧸ H) : transferFunction H g q ∈ transferSet H g := ⟨q, rfl⟩

variable (H) in
/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
/-
**Subgroup.transferTransversal** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：transferTransversal : H.LeftTransversal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed c
hoices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbi
ts in `G ⧸ H`.
-/
def transferTransversal : H.LeftTransversal :=
  ⟨transferSet H g, isComplement_range_left (coe_transferFunction g)⟩
/-
**Subgroup.transferTransversal_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：transferTransversal_apply (q : G ⧸ H) : ↑((transferTransversal H g).2.left
QuotientEquiv q) = transferFunction H g q
参数：q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement.leftQuotientEquiv_apply`：leftQuotientEquiv_apply {
f : G ⧸ H -> G} (hf : forall q, (f q : G ⧸ H) = q) (q : G ⧸ H) : (leftQuotientEq
uiv (isComplement_range_left hf) q …
· 使用引理 `Subgroup.coe_transferFunction`：coe_transferFunction (q : G ⧸ H) : ↑(tran
sferFunction H g q) = q
-/
lemma transferTransversal_apply (q : G ⧸ H) :
    ↑((transferTransversal H g).2.leftQuotientEquiv q) = transferFunction H g q :=
  IsComplement.leftQuotientEquiv_apply (coe_transferFunction g) q
/-
**Subgroup.transferTransversal_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k 
: ZMod (minimalPeriod (g • ·) q.out)) : ↑((transferTransversal H g).2.leftQuotie
ntEquiv (g ^ (cast k : Int) • q.out)) = g ^ (cast k : Int) * q.out.out
参数：q : orbitRel.Quotient (zpowers g) (G ⧸ H)；k : ZMod (minimalPeriod (g • ·) q.o
ut)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.transferTransversal_apply`：transferTransversal_apply (q : G ⧸ H
) : ↑((transferTransversal H g).2.leftQuotientEquiv q) = transferFunction H g q
· 使用引理 `Subgroup.transferFunction_apply`：transferFunction_apply (q : G ⧸ H) : tr
ansferFunction H g q = g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quot
ientEquivSigmaZMod H …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.quotientEquivSigmaZMod_symm_apply`：quotientEquivSigmaZMod_symm_
apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ZMod (minimalPeriod (g • 
·) q.out)) : (quotientEquivSigma…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : ℤ) • q.out)) =
      g ^ (cast k : ℤ) * q.out.out := by
  rw [transferTransversal_apply, transferFunction_apply, ← quotientEquivSigmaZMod_symm_apply,
    apply_symm_apply]
/-
**Subgroup.transferTransversal_apply''** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k
 : ZMod (minimalPeriod (g • ·) q.out)) : ↑((g • transferTransversal H g).2.leftQ
uotientEquiv (g ^ (cast k : Int) • q.out)) = if k = 0 then g ^ minimalPeriod (g 
• ·) q.out * q.out.out else g ^ (cast k : Int) * q.out.out
参数：q : orbitRel.Quotient (zpowers g) (G ⧸ H)；k : ZMod (minimalPeriod (g • ·) q.o
ut)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.smul_apply_eq_smul_apply_inv_smul`：smul_apply_eq_smul_apply_inv
_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) : ((f • S).2.leftQuotientEquiv
 q : G) = f • (S.2.leftQuotientE…
· 使用引理 `Subgroup.transferTransversal_apply`：transferTransversal_apply (q : G ⧸ H
) : ↑((transferTransversal H g).2.leftQuotientEquiv q) = transferFunction H g q
· 使用引理 `Subgroup.transferFunction_apply`：transferFunction_apply (q : G ⧸ H) : tr
ansferFunction H g q = g ^ (cast (quotientEquivSigmaZMod H g q).2 : Int) * (quot
ientEquivSigmaZMod H …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `Subgroup.quotientEquivSigmaZMod_apply`：quotientEquivSigmaZMod_apply (q :
 orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : Int) : quotientEquivSigmaZMod H g (
g ^ k • q.out) = ⟨q, k⟩
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `zpow_one_add`：zpow_one_add (a : G) (n : Int) : a ^ (1 + n) = a * a ^ n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZMod.intCast_cast`：intCast_cast (i : ZMod n) : ((cast i : Int) : R) = ca
st i
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `ZMod.cast_sub_one`：cast_sub_one {R : Type*} [Ring R] {n : Nat} (k : ZMod
 n) : (cast (k - 1 : ZMod n) : R) = (if k = 0 then (n : R) else cast k) - 1
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑((g • transferTransversal H g).2.leftQuotientEquiv (g ^ (cast k : ℤ) • q.out)) =
      if k = 0 then g ^ minimalPeriod (g • ·) q.out * q.out.out
      else g ^ (cast k : ℤ) * q.out.out := by
  rw [smul_apply_eq_smul_apply_inv_smul, transferTransversal_apply, transferFunction_apply, ←
    mul_smul, ← zpow_neg_one, ← zpow_add, quotientEquivSigmaZMod_apply, smul_eq_mul, ← mul_assoc,
    ← zpow_one_add, Int.cast_add, Int.cast_neg, Int.cast_one, intCast_cast, cast_id', id, ←
    sub_eq_neg_add, cast_sub_one, add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

end Subgroup

namespace MonoidHom

open MulAction Subgroup Subgroup.leftTransversals

/-- Given `ϕ : H →* A` from `H : Subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive /-- Given `ϕ : H →+ A` from `H : AddSubgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`. -/]
/-
**MonoidHom.transfer** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：transfer [FiniteIndex H] : G ->* A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def transfer [FiniteIndex H] : G →* A :=
  let T : H.LeftTransversal := default
  { toFun := fun g => diff ϕ T (g • T)
    map_one' := by rw [one_smul, diff_self]
    map_mul' := fun g h => by rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

variable (T : H.LeftTransversal)

@[to_additive]
/-
**MonoidHom.transfer_def** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transfer_def [FiniteIndex H] (g : G) : transfer ϕ g = diff ϕ T (g • T)
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.transfer.eq_1`：∀ {G : Type u_1} [inst : Group G] {H : Subgroup
 G} {A : Type u_2} [inst_1 : CommGroup A] (ϕ : ↥H →* A)   [inst_2 : H.FiniteInde
x],   ϕ.trans…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.leftTransversals.diff_mul_diff`：diff_mul_diff : diff ϕ R S * di
ff ϕ S T = diff ϕ R T
· 使用定理 `Subgroup.leftTransversals.smul_diff_smul`：smul_diff_smul (g : G) : diff 
ϕ (g • S) (g • T) = diff ϕ S T
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem transfer_def [FiniteIndex H] (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer, ← diff_mul_diff, ← smul_diff_smul, mul_comm, diff_mul_diff] <;> rfl

/-- Explicit computation of the transfer homomorphism. -/
/-
**MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot** 是 Mathlib 中的一个定理，位
于命名空间 `MonoidHom`。
形式化陈述：transfer_eq_prod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G) [F
intype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] : transfer ϕ g = ∏ q : Quotien
t (orbitRel (zpowers g) (G ⧸ H)), ϕ ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g
 • ·) q.out * q.out.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩
参数：g : G；Quotient (orbitRel (zpowers g) (G ⧸ H))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `QuotientGroup.out_conj_pow_minimalPeriod_mem`：∀ {G : Type u} [inst : Gro
up G] (H : Subgroup G) (g : G) (q : G ⧸ H),   (Quotient.out q)⁻¹ * g ^ Function.
minimalPeriod (fun x => g • x) q *…
· 使用定理 `MonoidHom.transfer_def`：transfer_def [FiniteIndex H] (g : G) : transfer 
ϕ g = diff ϕ T (g • T)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
· 使用定理 `Fintype.prod_congr`：prod_congr (f g : α -> M) (h : forall a, f a = g a) 
: ∏ a, f a = ∏ a, g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.transferTransversal_apply'`：transferTransversal_apply' (q : orb
itRel.Quotient (zpowers g) (G ⧸ H)) (k : ZMod (minimalPeriod (g • ·) q.out)) : ↑
((transferTransversal H g…
· 使用引理 `Subgroup.transferTransversal_apply''`：transferTransversal_apply'' (q : o
rbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ZMod (minimalPeriod (g • ·) q.out)) :
 ↑((g • transferTransversa…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Fintype.prod_eq_single`：prod_eq_single {f : α -> M} (a : α) (h : forall 
x != a, f x = 1) : ∏ x, f x = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ZMod.cast_zero`：cast_zero : (cast (0 : ZMod n) : R) = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
Explicit computation of the transfer homomorphism.
-/
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer ϕ g =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        ϕ
          ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩ := by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    transfer ϕ g = ∏ q : G ⧸ H, _ := transfer_def ϕ (transferTransversal H g) g
    _ = _ := ((quotientEquivSigmaZMod H g).symm.prod_comp _).symm
    _ = _ := Finset.prod_sigma _ _ _
    _ = _ := by
      refine Fintype.prod_congr _ _ (fun q => ?_)
      simp only [quotientEquivSigmaZMod_symm_apply, transferTransversal_apply',
        transferTransversal_apply'']
      rw [Fintype.prod_eq_single (0 : ZMod (Function.minimalPeriod (g • ·) q.out)) _]
      · simp only [if_pos, ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
      · intro k hk
        simp only [if_neg hk, inv_mul_cancel]
        exact map_one ϕ

open scoped IsMulCommutative in
/-- Auxiliary lemma in order to state `transfer_eq_pow`. -/
/-
**MonoidHom.transfer_eq_pow_aux** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transfer_eq_pow_aux (g : G) (key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k
 * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k) : g ^ H.index in H
参数：g : G；key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k
 * g₀ = g ^ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `QuotientGroup.out_conj_pow_minimalPeriod_mem`：∀ {G : Type u} [inst : Gro
up G] (H : Subgroup G) (g : G) (q : G ⧸ H),   (Quotient.out q)⁻¹ * g ^ Function.
minimalPeriod (fun x => g • x) q *…
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `Subgroup.prod_mem`：∀ {G : Type u_3} [inst : CommGroup G] (K : Subgroup G
) {ι : Type u_4} {t : Finset ι} {f : ι → G},   (∀ c ∈ t, f c ∈ K) → ∏ c ∈ t, f c
 ∈ K
· 使用引理 `Subgroup.index_eq_sum_minimalPeriod`：index_eq_sum_minimalPeriod (g : G) 
[Finite (G ⧸ H)] [Fintype (Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)))] :
 H.index = ∑ q : Quotient…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i

--- 原说明 ---
Auxiliary lemma in order to state `transfer_eq_pow`.
-/
theorem transfer_eq_pow_aux (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index ∈ H := by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  let := fintypeOfIndexNeZero hH
  classical
    replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H := fun k g₀ hk =>
      (congr_arg (· ∈ H) (key k g₀ hk)).mp hk
    replace key : ∀ q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q ∈ H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) → zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : ∀ q, f q ∈ H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q ∈ Finset.univ) => hf q
    simpa only [f, Finset.prod_pow_eq_pow_sum, index_eq_sum_minimalPeriod H g] using! key

open scoped IsMulCommutative in
/-
**MonoidHom.transfer_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transfer_eq_pow [FiniteIndex H] (g : G) (key : forall (k : Nat) (g₀ : G), 
g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k) : transfer ϕ g = ϕ ⟨g ^ H.i
ndex, transfer_eq_pow_aux g key⟩
参数：g : G；key : forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k
 * g₀ = g ^ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.transfer_eq_pow_aux`：transfer_eq_pow_aux (g : G) (key : forall
 (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k) : g ^ 
H.index in H
· 使用定理 `QuotientGroup.out_conj_pow_minimalPeriod_mem`：∀ {G : Type u} [inst : Gro
up G] (H : Subgroup G) (g : G) (q : G ⧸ H),   (Quotient.out q)⁻¹ * g ^ Function.
minimalPeriod (fun x => g • x) q *…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`：transfer_eq_p
rod_quotient_orbitRel_zpowers_quot [FiniteIndex H] (g : G) [Fintype (Quotient (o
rbitRel (zpowers g) (G ⧸ H)))] : transfer ϕ g =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_map_toList`：prod_map_toList (s : Finset ι) (f : ι -> M) : (s
.toList.map f).prod = s.prod f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `List.prod_map_hom`：prod_map_hom (L : List ι) (f : ι -> M) {G : Type*} [F
unLike G M N] [MonoidHomClass G M N] (g : G) : (L.map (g ∘ f)).prod = g (L.map f
).prod
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.coe_mk`：coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用引理 `Subgroup.index_eq_sum_minimalPeriod`：index_eq_sum_minimalPeriod (g : G) 
[Finite (G ⧸ H)] [Fintype (Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)))] :
 H.index = ∑ q : Quotient…
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.val_list_prod`：val_list_prod (l : List H) : (l.prod : G) = (l.m
ap Subtype.val).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem transfer_eq_pow [FiniteIndex H] (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
    let := H.fintypeQuotientOfFiniteIndex
    change ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key
    rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot, ← Finset.prod_map_toList,
      ← Function.comp_def ϕ, List.prod_map_hom]
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    rw [H.coe_mk, ← (zpowers g).coe_mk g (mem_zpowers g), ← (zpowers g).coe_pow,
      index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_map_toList]
    simp only [Subgroup.val_list_prod, List.map_map]
    congr 2
    funext
    apply key

open scoped IsMulCommutative in
/-
**MonoidHom.transfer_center_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transfer_center_eq_pow [FiniteIndex (center G)] (g : G) : transfer (Monoid
Hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
参数：center G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.transfer_eq_pow`：transfer_eq_pow [FiniteIndex H] (g : G) (key 
: forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k
) : transfer ϕ …
· 使用定理 `Subgroup.center.isMulCommutative`：∀ (G : Type u_1) [inst : Group G], IsM
ulCommutative ↥(Subgroup.center G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem transfer_center_eq_pow [FiniteIndex (center G)] (g : G) :
    transfer (MonoidHom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
  transfer_eq_pow (id (center G)) g fun k _ hk => by rw [← mul_right_inj, ← hk.comm,
    mul_inv_cancel_right]

variable (G) in
/-- The transfer homomorphism `G →* center G`. -/
/-
**MonoidHom.transferCenterPow** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：transferCenterPow [FiniteIndex (center G)] : G ->* center G where toFun g
参数：center G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfer homomorphism `G →* center G`.
-/
def transferCenterPow [FiniteIndex (center G)] : G →* center G where
  toFun g := ⟨g ^ (center G).index, (center G).pow_index_mem g⟩
  map_one' := Subtype.ext (one_pow (center G).index)
  map_mul' a b := by simp_rw [← show ∀ _, (_ : center G) = _ from transfer_center_eq_pow, map_mul]

@[simp]
/-
**MonoidHom.transferCenterPow_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transferCenterPow_apply [FiniteIndex (center G)] (g : G) : ↑(transferCente
rPow G g) = g ^ (center G).index
参数：center G；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transferCenterPow_apply [FiniteIndex (center G)] (g : G) :
    ↑(transferCenterPow G g) = g ^ (center G).index :=
  rfl

section BurnsideTransfer

variable {p : ℕ} (P : Sylow p G) (hP : normalizer P ≤ centralizer (P : Set G))
include hP

open scoped IsMulCommutative in
/-- The homomorphism `G →* P` in Burnside's transfer theorem. -/
/-
**MonoidHom.transferSylow** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：transferSylow [P.FiniteIndex] : G ->* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism `G →* P` in Burnside's transfer theorem.
-/
def transferSylow [P.FiniteIndex] : G →* P :=
  haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer (MonoidHom.id P)

variable [Fact p.Prime] [Finite (Sylow p G)]

/-- Auxiliary lemma in order to state `transferSylow_eq_pow`. -/
/-
**MonoidHom.transferSylow_eq_pow_aux** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transferSylow_eq_pow_aux (g : G) (hg : g in P) (k : Nat) (g₀ : G) (h : g₀⁻
¹ * g ^ k * g₀ in P) : g₀⁻¹ * g ^ k * g₀ = g ^ k
参数：g : G；hg : g in P；k : Nat；g₀ : G；h : g₀⁻¹ * g ^ k * g₀ in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.pow_mem`：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x 
: G}, x ∈ K → ∀ (n : ℕ), x ^ n ∈ K
· 使用定理 `Sylow.conj_eq_normalizer_conj_of_mem`：conj_eq_normalizer_conj_of_mem [Fa
ct p.Prime] [Finite (Sylow p G)] (P : Sylow p G) [_hP : IsMulCommutative P] (x g
 : G) (hx : x in P) (hy : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.inv_mul_cancel`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Com
mute a b → a⁻¹ * b * a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Auxiliary lemma in order to state `transferSylow_eq_pow`.
-/
theorem transferSylow_eq_pow_aux (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G)
    (h : g₀⁻¹ * g ^ k * g₀ ∈ P) : g₀⁻¹ * g ^ k * g₀ = g ^ k := by
  have : IsMulCommutative P :=
    ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  replace hg := P.pow_mem hg k
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h
  exact h.trans (Commute.inv_mul_cancel (hP hn (g ^ k) hg).symm)

variable [P.FiniteIndex]

open scoped IsMulCommutative in
/-
**MonoidHom.transferSylow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：transferSylow_eq_pow (g : G) (hg : g in P) : transferSylow P hP g = ⟨g ^ P
.index, transfer_eq_pow_aux g (transferSylow_eq_pow_aux P hP g hg)⟩
参数：g : G；hg : g in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.transfer_eq_pow`：transfer_eq_pow [FiniteIndex H] (g : G) (key 
: forall (k : Nat) (g₀ : G), g₀⁻¹ * g ^ k * g₀ in H -> g₀⁻¹ * g ^ k * g₀ = g ^ k
) : transfer ϕ …
· 使用定理 `MonoidHom.transferSylow_eq_pow_aux`：transferSylow_eq_pow_aux (g : G) (hg
 : g in P) (k : Nat) (g₀ : G) (h : g₀⁻¹ * g ^ k * g₀ in P) : g₀⁻¹ * g ^ k * g₀ =
 g ^ k
-/
theorem transferSylow_eq_pow (g : G) (hg : g ∈ P) :
    transferSylow P hP g =
      ⟨g ^ P.index, transfer_eq_pow_aux g (transferSylow_eq_pow_aux P hP g hg)⟩ :=
  haveI : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
  transfer_eq_pow _ _ <| transferSylow_eq_pow_aux P hP g hg
/-
**MonoidHom.transferSylow_domRestrict_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHo
m`。
形式化陈述：transferSylow_domRestrict_eq_pow : ⇑((transferSylow P hP).domRestrict (P :
 Subgroup G)) = (fun x : P => x ^ (P : Subgroup G).index)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Sylow.instSubgroupClass`：∀ {p : ℕ} {G : Type u_1} [inst : Group G], Subg
roupClass (Sylow p G) G
· 使用定理 `MonoidHom.transferSylow_eq_pow`：transferSylow_eq_pow (g : G) (hg : g in 
P) : transferSylow P hP g = ⟨g ^ P.index, transfer_eq_pow_aux g (transferSylow_e
q_pow_aux P hP g hg)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem transferSylow_domRestrict_eq_pow : ⇑((transferSylow P hP).domRestrict (P : Subgroup G)) =
    (fun x : P => x ^ (P : Subgroup G).index) :=
  funext fun g => transferSylow_eq_pow P hP g g.2

@[deprecated (since := "2026-07-19")]
alias transferSylow_restrict_eq_pow := transferSylow_domRestrict_eq_pow

/-- **Burnside's normal p-complement theorem**: If `N(P) ≤ C(P)`, then `P` has a normal
complement. -/
/-
**MonoidHom.ker_transferSylow_isComplement'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom
`。
形式化陈述：ker_transferSylow_isComplement' : IsComplement' (transferSylow P hP).ker P
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Sylow.instSubgroupClass`：∀ {p : ℕ} {G : Type u_1} [inst : Group G], Subg
roupClass (Sylow p G) G
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.transferSylow_domRestrict_eq_pow`：transferSylow_domRestrict_eq
_pow : ⇑((transferSylow P hP).domRestrict (P : Subgroup G)) = (fun x : P => x ^ 
(P : Subgroup G).index)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.domRestrict_range`：domRestrict_range (f : G ->* N) : (f.domRes
trict K).range = K.map f
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `Subgroup.map_le_range`：map_le_range (H : Subgroup G) : map f H <= f.rang
e
· 使用定理 `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`：∀ {G : Type u_1} [in
st : Group G] {H K : Subgroup G}, Disjoint H K → ↑H * ↑K = Set.univ → H.IsComple
ment' K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.coe_top`：coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `MonoidHom.ker_domRestrict`：ker_domRestrict (f : G ->* M) : (f.domRestric
t K).ker = f.ker.subgroupOf K
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `Subgroup.normal_mul`：normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H
) : Set G) = N * H
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Burnside's normal p-complement theorem**: If `N(P) ≤ C(P)`, then `P` has a nor
mal
complement.
-/
theorem ker_transferSylow_isComplement' : IsComplement' (transferSylow P hP).ker P := by
  have hf : Function.Bijective ((transferSylow P hP).domRestrict (P : Subgroup G)) :=
    (transferSylow_domRestrict_eq_pow P hP).symm ▸ (P.2.powEquiv' P.not_dvd_index).bijective
  rw [Function.Bijective, ← range_eq_top, domRestrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans
    (map_le_range (transferSylow P hP) P)))
  rw [← (comap_injective this).eq_iff, comap_top, comap_map_eq, sup_comm, SetLike.ext'_iff,
    normal_mul, ← ker_eq_bot_iff, ← map_subtype_inj,
    ker_domRestrict, subgroupOf_map_subtype, Subgroup.map_bot, coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2
/-
**MonoidHom.not_dvd_card_ker_transferSylow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`
。
形式化陈述：not_dvd_card_ker_transferSylow : ¬p ∣ Nat.card (transferSylow P hP).ker
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Subgroup.IsComplement'.index_eq_card`：∀ {G : Type u_1} [inst : Group G] 
{H K : Subgroup G}, H.IsComplement' K → K.index = Nat.card ↥H
· 使用定理 `MonoidHom.ker_transferSylow_isComplement'`：ker_transferSylow_isComplemen
t' : IsComplement' (transferSylow P hP).ker P
-/
theorem not_dvd_card_ker_transferSylow : ¬p ∣ Nat.card (transferSylow P hP).ker :=
  (ker_transferSylow_isComplement' P hP).index_eq_card ▸ P.not_dvd_index
/-
**MonoidHom.ker_transferSylow_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_transferSylow_disjoint (Q : Subgroup G) (hQ : IsPGroup p Q) : Disjoint
 (transferSylow P hP).ker Q
参数：Q : Subgroup G；hQ : IsPGroup p Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.card_eq_one`：card_eq_one : Nat.card H = 1 ↔ H = ⊥
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsPGroup.card_eq_or_dvd`：card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card 
G
· 使用定理 `IsPGroup.to_le`：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <=
 K) : IsPGroup p H
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `MonoidHom.not_dvd_card_ker_transferSylow`：not_dvd_card_ker_transferSylow
 : ¬p ∣ Nat.card (transferSylow P hP).ker
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Subgroup.card_dvd_of_le`：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K
) : Nat.card H ∣ Nat.card K
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem ker_transferSylow_disjoint (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Disjoint (transferSylow P hP).ker Q :=
  disjoint_iff.mpr <|
    card_eq_one.mp <|
      (hQ.to_le inf_le_right).card_eq_or_dvd.resolve_right fun h =>
        not_dvd_card_ker_transferSylow P hP <| h.trans <| card_dvd_of_le inf_le_left

end BurnsideTransfer

end MonoidHom

namespace IsCyclic

open Subgroup

-- we could suppress the variable `p`, but that might introduce `motive not type correct` issues.
variable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : (Nat.card G).minFac = p) {P : Sylow p G}

include hp in
/-
**IsCyclic.normalizer_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclic`。
形式化陈述：normalizer_le_centralizer (hP : IsCyclic P) : normalizer P <= centralizer 
(P : Set G)
参数：hP : IsCyclic P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Subgroup.card_dvd_of_injective`：card_dvd_of_injective (f : α ->* H) (hf 
: Function.Injective f) : Nat.card α ∣ Nat.card H
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `QuotientGroup.kerLift_injective`：kerLift_injective : Injective (kerLift 
φ)
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `IsPGroup.exists_card_eq`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [Fact
 (Nat.Prime p)] [Finite G], IsPGroup p G → ∃ n, Nat.card G = p ^ n
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsCyclic.card_mulAut`：IsCyclic.card_mulAut [Group G] [Finite G] [h : IsC
yclic G] : Nat.card (MulAut G) = Nat.totient (Nat.card G)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.totient_one`：totient_one : φ 1 = 1
· 使用定理 `Nat.coprime_one_right`：∀ (n : ℕ), n.Coprime 1
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Nat.Coprime.pow_right`：∀ {k m : ℕ} (n : ℕ), k.Coprime m → k.Coprime (m ^
 n)
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
· 使用定理 `Subgroup.relIndex_dvd_of_le_left`：relIndex_dvd_of_le_left (hHK : H <= K)
 : K.relIndex L ∣ H.relIndex L
· 使用定理 `Subgroup.le_centralizer`：le_centralizer [h : IsMulCommutative H] : H <= 
centralizer H
· 使用定理 `Subgroup.relIndex_dvd_index_of_le`：relIndex_dvd_index_of_le (h : H <= K)
 : H.relIndex K ∣ H.index
（共 57 条，此处仅展示前 30 条）
-/
theorem normalizer_le_centralizer (hP : IsCyclic P) :
    normalizer P ≤ centralizer (P : Set G) := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (normalizer _) (centralizer P)]
  have := Fact.mk (Nat.minFac_prime hn)
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut, hk, Nat.totient_prime_pow Fact.out h0]
  refine (Nat.Coprime.pow_right _ ?_).mul_right ?_
  · apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact P.not_dvd_index
  · apply Nat.Coprime.coprime_dvd_left <| relIndex_dvd_card ..
    apply Nat.Coprime.coprime_dvd_left <| card_subgroup_dvd_card _
    have h1 := Nat.gcd_dvd_left (Nat.card G) ((Nat.card G).minFac - 1)
    have h2 := Nat.gcd_le_right (n := (Nat.card G).minFac - 1) (Nat.card G)
      (tsub_pos_iff_lt.mpr (Nat.minFac_prime hn).one_lt)
    contrapose! h2
    refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos (Nat.minFac_le_of_dvd ?_ h1)
    exact (Nat.two_le_iff _).mpr ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

include hp in
/-- A cyclic Sylow subgroup for the smallest prime has a normal complement. -/
/-
**IsCyclic.isComplement'** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclic`。
形式化陈述：isComplement' (hP : IsCyclic P) : (MonoidHom.transferSylow P (hP.normalize
r_le_centralizer hp)).ker.IsComplement' P
参数：hP : IsCyclic P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.normalizer_le_centralizer`：normalizer_le_centralizer (hP : IsCy
clic P) : normalizer P <= centralizer (P : Set G)
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subgroup.isComplement'_bot_top`：∀ {G : Type u_1} [inst : Group G], ⊥.IsC
omplement' ⊤
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `MonoidHom.ker_transferSylow_isComplement'`：ker_transferSylow_isComplemen
t' : IsComplement' (transferSylow P hP).ker P
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A

--- 原说明 ---
A cyclic Sylow subgroup for the smallest prime has a normal complement.
-/
theorem isComplement' (hP : IsCyclic P) :
    (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker.IsComplement' P := by
  subst hp
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)).ker ⊥,
      Subsingleton.elim P.1 ⊤]
    exact isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (hP.normalizer_le_centralizer rfl)

end IsCyclic

