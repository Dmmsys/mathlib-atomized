/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Quotienting out a free `ℤ`-module

If `G` is a rank `d` free `ℤ`-module, then `G/nG` is a finite group of cardinality `n ^ d`.
-/

@[expose] public section

open Finsupp Function Module

variable {G H M : Type*} [AddCommGroup G] {n : ℕ}

variable (G n) in
/-- `ModN G n` denotes the quotient of `G` by multiples of `n` -/
/-
**ModN** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModN : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModN G n` denotes the quotient of `G` by multiples of `n`
-/
abbrev ModN : Type _ := G ⧸ LinearMap.range (LinearMap.lsmul ℤ G n)

namespace ModN

/-
**ModN.** 是 Mathlib 中的一个实例，位于命名空间 `ModN`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (ZMod n) (ModN G n) := QuotientAddGroup.zmodModule (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The universal property of `ModN G n` in terms of monoids: Monoid homomorphisms from `ModN G n`
are the same as monoid homomorphisms from `G` whose values are `n`-torsion. -/
/-
**ModN.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModN`。
形式化陈述：{G : Type u_1} →   {M : Type u_3} →     [inst : AddCommGroup G] → {n : ℕ} 
→ [inst_1 : AddMonoid M] → (ModN G n →+ M) ≃ { φ // ∀ (g : G), n • φ g = 0 }
参数：ModN G n →+ M；g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of `ModN G n` in terms of monoids: Monoid homomorphisms f
rom `ModN G n`
are the same as monoid homomorphisms from `G` whose values are `n`-torsion.
-/
protected def liftEquiv [AddMonoid M] : (ModN G n →+ M) ≃ {φ : G →+ M // ∀ g, n • φ g = 0} where
  toFun f := ⟨f.comp (QuotientAddGroup.mk' _), fun g ↦ by
    let Gn : AddSubgroup G := (LinearMap.range (LinearMap.lsmul ℤ G n)).toAddSubgroup
    suffices n • g ∈ (QuotientAddGroup.mk' Gn).ker by
      simp only [AddMonoidHom.coe_comp, comp_apply, ← map_nsmul]
      change f (QuotientAddGroup.mk' Gn (n • g)) = 0 -- Can we avoid `change`?
      rw [this, map_zero]
    simp [QuotientAddGroup.ker_mk', Gn]⟩
  invFun φ := QuotientAddGroup.lift _ φ <| by rintro - ⟨g, rfl⟩; simpa using φ.property g
  left_inv f := by
    ext x
    induction x using QuotientAddGroup.induction_on
    rfl -- Should `simp` suffice here?
  right_inv φ := by aesop

/-- The universal property of `ModN G n` in terms of `ZMod n`-modules: `ZMod n`-linear maps from
`ModN G n` are the same as monoid homomorphisms from `G` whose values are `n`-torsion. -/
/-
**ModN.liftEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `ModN`。
形式化陈述：{G : Type u_1} →   {H : Type u_2} →     [inst : AddCommGroup G] →       {n
 : ℕ} →         [inst_1 : AddCommGroup H] →           [inst_2 : _root_.Module (Z
Mod n) H] → (ModN G n →ₗ[ZMod n] H) ≃ { φ // ∀ (g : G), n • φ g = 0 }
参数：ZMod n；ModN G n →ₗ[ZMod n] H；g : G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The universal property of `ModN G n` in terms of `ZMod n`-modules: `ZMod n`-line
ar maps from
`ModN G n` are the same as monoid homomorphisms from `G` whose values are `n`-to
rsion.
-/
protected def liftEquiv' [AddCommGroup H] [Module (ZMod n) H] :
    (ModN G n →ₗ[ZMod n] H) ≃ {φ : G →+ H // ∀ g, n • φ g = 0} :=
  (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans ModN.liftEquiv

variable (n) in
/-- The quotient map `G → G / nG`. -/
/-
**ModN.mkQ** 是 Mathlib 中的一个定义，位于命名空间 `ModN`。
形式化陈述：mkQ : G ->+ ModN G n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map `G → G / nG`.
-/
def mkQ : G →+ ModN G n := (LinearMap.range (LinearMap.lsmul ℤ G n)).mkQ

variable [NeZero n]

set_option backward.isDefEq.respectTransparency false in
/-- Given a free module `G` over `ℤ`, construct the corresponding basis
of `G / ⟨n⟩` over `ℤ / nℤ`. -/
/-
**ModN.basis** 是 Mathlib 中的一个定义，位于命名空间 `ModN`。
形式化陈述：basis {ι : Type*} (b : Basis ι Int G) : Basis ι (ZMod n) (ModN G n)
参数：b : Basis ι Int G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a free module `G` over `ℤ`, construct the corresponding basis
of `G / ⟨n⟩` over `ℤ / nℤ`.
-/
noncomputable def basis {ι : Type*} (b : Basis ι ℤ G) : Basis ι (ZMod n) (ModN G n) := by
  set nG := LinearMap.range (LinearMap.lsmul ℤ G n)
  set H := G ⧸ nG
  set φ : G →ₗ[ℤ] H := nG.mkQ
  let mod : (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G →ₗ[ℤ] (ι →₀ ℤ) := b.repr
  have hker : nG ≤ LinearMap.ker (mod.comp f) := by
    rintro _ ⟨x, rfl⟩
    ext b
    simp [mod, f]
  let g : H →ₗ[ℤ] (ι →₀ ZMod n) := nG.liftQ (mod.comp f) hker
  refine ⟨.ofBijective (g.toAddMonoidHom.toZModLinearMap n) ⟨?_, ?_⟩⟩
  · rw [AddMonoidHom.coe_toZModLinearMap, LinearMap.toAddMonoidHom_coe, injective_iff_map_eq_zero,
      nG.mkQ_surjective.forall]
    intro x hx
    simp only [Submodule.mkQ_apply, g] at hx
    rw [Submodule.liftQ_apply] at hx
    replace hx : ∀ b, ↑n ∣ f x b := by
      simpa [mod, DFunLike.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd] using! hx
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    choose c hc using hx
    refine ⟨b.repr.symm ⟨(f x).support, c, by simp [hc, NeZero.ne]⟩, b.repr.injective ?_⟩
    simpa [DFunLike.ext_iff, eq_comm] using! hc
  · suffices mod ∘ b.repr = g ∘ nG.mkQ by
      exact (this ▸ (mapRange_surjective _ (map_zero _) ZMod.intCast_surjective).comp
        b.repr.surjective).of_comp
    ext x b
    simp [mod, g, f, H]

set_option backward.isDefEq.respectTransparency false in
/-
**ModN.basis_apply_eq_mkQ** 是 Mathlib 中的一个引理，位于命名空间 `ModN`。
形式化陈述：basis_apply_eq_mkQ {ι : Type*} (b : Basis ι Int G) (i : ι) : basis b i = m
kQ n (b i)
参数：b : Basis ι Int G；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basis_apply_eq_mkQ {ι : Type*} (b : Basis ι ℤ G) (i : ι) : basis b i = mkQ n (b i) := by
  rw [Basis.apply_eq_iff]; simp [basis, mkQ]

variable [Module.Free ℤ G] [Module.Finite ℤ G]
/-
**ModN.instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 `ModN`。
形式化陈述：instModuleFinite : Module.Finite (ZMod n) (ModN G n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance instModuleFinite : Module.Finite (ZMod n) (ModN G n) :=
  .of_basis <| basis <| Module.Free.chooseBasis ℤ G
/-
**ModN.instFinite** 是 Mathlib 中的一个实例，位于命名空间 `ModN`。
形式化陈述：instFinite : Finite (ModN G n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance instFinite : Finite (ModN G n) := Module.finite_of_finite (ZMod n)

variable (G n)
/-
**ModN.natCard_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModN`。
形式化陈述：∀ (G : Type u_1) [inst : AddCommGroup G] (n : ℕ) [NeZero n] [Module.Free ℤ
 G] [Module.Finite ℤ G],   Nat.card (ModN G n) = n ^ Module.finrank ℤ G
参数：G : Type u_1；n : ℕ；ModN G n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_finsupp`：∀ (ι : Type u_1) (α : Type u_2) [inst : DecidableE
q ι] [inst_1 : Fintype ι] [inst_2 : Zero α] [inst_3 : Fintype α],   Fintype.card
 (ι →₀ α) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma natCard_eq : Nat.card (ModN G n) = n ^ Module.finrank ℤ G := by
  simp [Nat.card_congr (basis <| Module.Free.chooseBasis ℤ G).repr.toEquiv,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_chooseBasisIndex]

end ModN

