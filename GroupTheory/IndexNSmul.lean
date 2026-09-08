/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Lemmas about index and multiplication-by-n

In this file we collect some results involving the multiplication-by-`n` map
`nsmulAddMonoidHom n` (for a natural number `n`) on a commutative additive group
and the (relative) index of subgroups.
-/

public section

namespace AddSubgroup

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

open Module

open QuotientAddGroup in
variable (M) in
/-- The index of the image of the multiplication-by-`n` map on an additive group `M` that is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ M`. -/
/-
**AddSubgroup.index_range_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：index_range_nsmul [Free Int M] [Module.Finite Int M] (n : Nat) : (nsmulAdd
MonoidHom (α
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.map_range_nsmulAddMonoidHom`：∀ {M : Type u_5} {N : Type u_6} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup N] (e : M ≃+ N) (n : ℕ),   AddSubgr
oup.map (↑e) (nsmulAddMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.index_map_equiv`：∀ {G : Type u_1} {G' : Type u_2} [inst : Ad
dGroup G] [inst_1 : AddGroup G'] (H : AddSubgroup G) (e : G ≃+ G'),   (AddSubgro
up.map (↑e) H).in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `Pi.isAddCommutative`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I) → 
Add (f i)] [∀ (i : I), IsAddCommutative (f i)],   IsAddCommutative ((i : I) → f 
i)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Int.range_nsmulAddMonoidHom`：range_nsmulAddMonoidHom (n : Nat) : (nsmulA
ddMonoidHom n).range = zmultiples (n : Int)
· 使用定理 `Nat.card_fun`：card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat
.card α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The index of the image of the multiplication-by-`n` map on an additive group `M`
 that is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ M`.
-/
lemma index_range_nsmul [Free ℤ M] [Module.Finite ℤ M] (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = n ^ finrank ℤ M :=
  calc
    _ = (nsmulAddMonoidHom (α := (Fin (finrank ℤ M) → ℤ)) n).range.index := by
      simpa [AddEquiv.map_range_nsmulAddMonoidHom]
        using (index_map_equiv (nsmulAddMonoidHom (α := M) n).range
                (Module.finBasis ℤ M).equivFun.toAddEquiv).symm
    _ = _ := by
      simp [index_eq_card, Nat.card_congr (addEquivPiModRangeNSMulAddMonoidHom _ n).toEquiv,
        Nat.card_fun, Int.range_nsmulAddMonoidHom,
        Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv]

/-- The relative index in `S` of the image of the multiplication-by-`n` map
on an additive subgroup `S` of an additive group such that `S` is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ S`. -/
/-
**AddSubgroup.relIndex_map_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：relIndex_map_nsmul (n : Nat) (S : AddSubgroup M) [Free Int ↥S.toIntSubmodu
le] [Module.Finite Int ↥S.toIntSubmodule] : (S.map (nsmulAddMonoidHom (α
参数：n : Nat；S : AddSubgroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range`：∀ {M : Type u_
6} [inst : AddCommGroup M] (S : AddSubgroup M) (n : ℕ),   (AddSubgroup.map (nsmu
lAddMonoidHom n) S).addSubgroupOf S = (nsmulAd…
· 使用引理 `AddSubgroup.index_range_nsmul`：index_range_nsmul [Free Int M] [Module.Fi
nite Int M] (n : Nat) : (nsmulAddMonoidHom (α

--- 原说明 ---
The relative index in `S` of the image of the multiplication-by-`n` map
on an additive subgroup `S` of an additive group such that `S` is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ S`.
-/
lemma relIndex_map_nsmul (n : ℕ) (S : AddSubgroup M) [Free ℤ ↥S.toIntSubmodule]
    [Module.Finite ℤ ↥S.toIntSubmodule] :
    (S.map (nsmulAddMonoidHom (α := M) n)).relIndex S = n ^ finrank ℤ S := by
  simpa only [relIndex, addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using! index_range_nsmul S.toIntSubmodule n

/-- On an additive group that is torsion-free as a `ℤ`-module, the linear map given by
multiplication by `n : ℕ` is injective (when `n ≠ 0`). -/
/-
**AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree** 是 Mathlib 中的一个
引理，位于命名空间 `AddSubgroup`。
形式化陈述：distribSMulToLinearMap_injective_of_isTorsionFree [IsTorsionFree Int M] {n
 : Nat} (hn : n != 0) : Function.Injective (DistribSMul.toLinearMap Int M n)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
On an additive group that is torsion-free as a `ℤ`-module, the linear map given 
by
multiplication by `n : ℕ` is injective (when `n ≠ 0`).
-/
lemma distribSMulToLinearMap_injective_of_isTorsionFree [IsTorsionFree ℤ M] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (DistribSMul.toLinearMap ℤ M n) :=
  LinearMap.ker_eq_bot.mp <| (Submodule.eq_bot_iff _).mpr fun x hx ↦ by simp_all

/-- On an additive group that is torsion-free as a `ℤ`-module, the multiplication-by-`n` map
is injective (when `n ≠ 0`). -/
/-
**AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree** 是 Mathlib 中的一个引理，位于
命名空间 `AddSubgroup`。
形式化陈述：nsmulAddMonoidHom_injective_of_isTorsionFree [IsTorsionFree Int M] {n : Na
t} (hn : n != 0) : Function.Injective (nsmulAddMonoidHom (α
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHom.ker_eq_bot_iff`：∀ {G : Type u_1} [inst : AddGroup G] {M : T
ype u_7} [inst_1 : AddZeroClass M] (f : G →+ M),   f.ker = ⊥ ↔ Function.Injectiv
e ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubgroup.eq_bot_iff_forall`：∀ {G : Type u_1} [inst : AddGroup G] (H :
 AddSubgroup G), H = ⊥ ↔ ∀ x ∈ H, x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmulAddMonoidHom_apply`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : 
ℕ) (x : α), (nsmulAddMonoidHom n) x = n • x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
On an additive group that is torsion-free as a `ℤ`-module, the multiplication-by
-`n` map
is injective (when `n ≠ 0`).
-/
lemma nsmulAddMonoidHom_injective_of_isTorsionFree [IsTorsionFree ℤ M] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (nsmulAddMonoidHom (α := M) n) :=
  (AddMonoidHom.ker_eq_bot_iff _).mp <| (eq_bot_iff_forall _).mpr fun x hx ↦ by simp_all

/-- If `A` is a subgroup of finite index of an additive group `M` that is finitely generated
and torsion-free as a `ℤ`-module, then `A` and `M` have the same rank. -/
/-
**AddSubgroup.finrank_eq_of_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：finrank_eq_of_finiteIndex [Module.Finite Int M] [IsTorsionFree Int M] (A :
 AddSubgroup M) [A.FiniteIndex] : finrank Int A = finrank Int M
参数：A : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `LinearMap.finrank_range_of_inj`：LinearMap.finrank_range_of_inj {f : M ->
ₗ[R] N} (hf : Function.Injective f) : finrank R (LinearMap.range f) = finrank R 
M
· 使用引理 `AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree`：distribSM
ulToLinearMap_injective_of_isTorsionFree [IsTorsionFree Int M] {n : Nat} (hn : n
 != 0) : Function.Injective (DistribSMul.toLinearMa…
· 使用定理 `AddSubgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_3} {inst : AddGroup
 G} {H : AddSubgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.symm_apply_le`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [i
nst_1 : LE β] (e : α ≃o β) {x : α} {y : β}, e.symm y ≤ x ↔ y ≤ e x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `AddSubgroup.nsmul_index_mem`：∀ {G : Type u_6} [inst : AddGroup G] (H : A
ddSubgroup G) [H.Normal] (g : G), H.index • g ∈ H
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G

--- 原说明 ---
If `A` is a subgroup of finite index of an additive group `M` that is finitely g
enerated
and torsion-free as a `ℤ`-module, then `A` and `M` have the same rank.
-/
lemma finrank_eq_of_finiteIndex [Module.Finite ℤ M] [IsTorsionFree ℤ M] (A : AddSubgroup M)
    [A.FiniteIndex] :
    finrank ℤ A = finrank ℤ M := by
  refine le_antisymm A.toIntSubmodule.finrank_le ?_
  have : finrank ℤ (DistribSMul.toLinearMap ℤ M A.index).range = finrank ℤ M :=
    (DistribSMul.toLinearMap ..).finrank_range_of_inj <|
      distribSMulToLinearMap_injective_of_isTorsionFree FiniteIndex.index_ne_zero
  rw [← this]
  refine Submodule.finrank_mono <| (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ x, A.index • x = m := by simpa using hm
  exact A.nsmul_index_mem x

/-- If `A ≤ B` are subgroups of an additive group `M` such that `A` has finite relative index
in `B`, where `B` is finitely generated and torsion-free as a `ℤ`-module, then `A` and `B`
have the same rank. -/
/-
**AddSubgroup.finrank_eq_of_isFiniteRelIndex** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgr
oup`。
形式化陈述：finrank_eq_of_isFiniteRelIndex {A B : AddSubgroup M} [Module.Finite Int B]
 [IsTorsionFree Int B] (h : A <= B) [A.IsFiniteRelIndex B] : finrank Int A = fin
rank Int B
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.IsFiniteRelIndex.to_finiteIndex_addSubgroupOf`：∀ {G : Type u
_1} [inst : AddGroup G] {H K : AddSubgroup G} [H.IsFiniteRelIndex K], (H.addSubg
roupOf K).FiniteIndex
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddSubgroup.finrank_eq_of_finiteIndex`：finrank_eq_of_finiteIndex [Module
.Finite Int M] [IsTorsionFree Int M] (A : AddSubgroup M) [A.FiniteIndex] : finra
nk Int A = finrank Int M
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N

--- 原说明 ---
If `A ≤ B` are subgroups of an additive group `M` such that `A` has finite relat
ive index
in `B`, where `B` is finitely generated and torsion-free as a `ℤ`-module, then `
A` and `B`
have the same rank.
-/
lemma finrank_eq_of_isFiniteRelIndex {A B : AddSubgroup M} [Module.Finite ℤ B] [IsTorsionFree ℤ B]
    (h : A ≤ B) [A.IsFiniteRelIndex B] :
    finrank ℤ A = finrank ℤ B := by
  have : (A.addSubgroupOf B).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_addSubgroupOf
  rw [← finrank_eq_of_finiteIndex (A.addSubgroupOf B)]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

end AddSubgroup

end

