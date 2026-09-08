/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.RingTheory.Finiteness.Nilpotent
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Filter.Cofinite

/-!
# Chains of roots and weights

Given roots `α` and `β` of a Lie algebra, together with elements `x` in the `α`-root space and
`y` in the `β`-root space, it follows from the Leibniz identity that `⁅x, y⁆` is either zero or
belongs to the `α + β`-root space. Iterating this operation leads to the study of families of
roots of the form `k • α + β`. Such a family is known as the `α`-chain through `β` (or sometimes,
the `α`-string through `β`) and the study of the sum of the corresponding root spaces is an
important technique.

More generally if `α` is a root and `χ` is a weight of a representation, it is useful to study the
`α`-chain through `χ`.

We provide basic definitions and results to support `α`-chain techniques in this file.

## Main definitions / results

* `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
  find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
  trivial.
* `LieModule.genWeightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`,
  this is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
* `LieModule.trace_toEnd_genWeightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
  subalgebra `H`, there is a natural ideal `corootSpace α` in `H`. This lemma
  states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
  `α`-chain, provided the weight spaces at the endpoints are both trivial.
* `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`: given a (potential) root
  `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
  `corootSpace α` of `H`, we may find an integral linear combination between
  `α` and any weight `χ` of a representation.

## TODO

It should be possible to unify some of the definitions here such as `LieModule.chainBotCoeff`,
`LieModule.chainTopCoeff` with corresponding definitions such as `RootPairing.chainBotCoeff`,
`RootPairing.chainTopCoeff`. This is not quite trivial since:
* The definitions here allow for chains in representations of Lie algebras.
* The proof that the roots of a Lie algebra are a root system currently depends on these results.
  (This can be resolved by proving the root reflection formula using the approach outlined in
  Bourbaki Ch. VIII §2.2 Lemma 1 (page 80 of English translation, 88 of English PDF).)

-/

@[expose] public section

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

section

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)
include hχ₁

/-
**LieModule.eventually_genWeightSpace_smul_add_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 
`LieModule`。
形式化陈述：eventually_genWeightSpace_smul_add_eq_bot : forallᶠ (k : Nat) in Filter.at
Top, genWeightSpace M (k • χ₁ + χ₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `Pi.instIsAddTorsionFree`：∀ {ι : Type u_1} {M : ι → Type u_3} [inst : (i 
: ι) → AddMonoid (M i)] [∀ (i : ι), IsAddTorsionFree (M i)],   IsAddTorsionFree 
((i : ι) → M …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `LieModule.finite_genWeightSpace_ne_bot`：finite_genWeightSpace_ne_bot [Is
Noetherian R M] : {χ : L -> R | genWeightSpace M χ != ⊥}.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
-/
lemma eventually_genWeightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : ℕ → L → R := fun k ↦ k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, ← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : ℤ) • χ₁ = (l : ℤ) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
  exact Nat.cast_inj.mp <| smul_left_injective ℤ hχ₁ hkl
/-
**LieModule.exists_genWeightSpace_smul_add_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Module`。
形式化陈述：exists_genWeightSpace_smul_add_eq_bot : exists k > 0, genWeightSpace M (k 
• χ₁ + χ₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `Nat.eventually_pos`：Nat.eventually_pos : forallᶠ (k : Nat) in Filter.atT
op, 0 < k
· 使用引理 `LieModule.eventually_genWeightSpace_smul_add_eq_bot`：eventually_genWeigh
tSpace_smul_add_eq_bot : forallᶠ (k : Nat) in Filter.atTop, genWeightSpace M (k 
• χ₁ + χ₂) = ⊥
-/
lemma exists_genWeightSpace_smul_add_eq_bot :
    ∃ k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ :=
  (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists
/-
**LieModule.exists** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists₂_genWeightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

/-- Given two (potential) weights `χ₁` and `χ₂` together with integers `p` and `q`, it is often
useful to study the sum of weight spaces associated to the family of weights `k • χ₁ + χ₂` for
`p < k < q`. -/
/-
**LieModule.genWeightSpaceChain** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：genWeightSpaceChain : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two (potential) weights `χ₁` and `χ₂` together with integers `p` and `q`, 
it is often
useful to study the sum of weight spaces associated to the family of weights `k 
• χ₁ + χ₂` for
`p < k < q`.
-/
def genWeightSpaceChain : LieSubmodule R L M :=
  ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂)
/-
**LieModule.genWeightSpaceChain_def** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：genWeightSpaceChain_def : genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k in Ioo p q
, genWeightSpace M (k • χ₁ + χ₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma genWeightSpaceChain_def :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂) :=
  rfl
/-
**LieModule.genWeightSpaceChain_def'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：genWeightSpaceChain_def' : genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k in Finset
.Ioo p q, genWeightSpace M (k • χ₁ + χ₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma genWeightSpaceChain_def' :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Finset.Ioo p q, genWeightSpace M (k • χ₁ + χ₂) := by
  have : ∀ (k : ℤ), k ∈ Ioo p q ↔ k ∈ Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]

@[simp]
/-
**LieModule.genWeightSpaceChain_neg** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：genWeightSpaceChain_neg : genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = genWe
ightSpaceChain M χ₁ χ₂ p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_involutive`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Invo
lutive Neg.neg
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.biSup_comp`：Equiv.biSup_comp {ι ι' : Type*} {g : ι' -> α} (e : ι ≃
 ι') (s : Set ι') : ⨆ i in e.symm '' s, g (e i) = ⨆ i in s, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `Set.neg_Ioo`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialO
rder α] [IsOrderedAddMonoid α] (a b : α),   -Set.Ioo a b = Set.Ioo (-b) (-a)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma genWeightSpaceChain_neg :
    genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = genWeightSpaceChain M χ₁ χ₂ p q := by
  let e : ℤ ≃ ℤ := neg_involutive.toPerm
  simp_rw [genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo]
/-
**LieModule.genWeightSpace_le_genWeightSpaceChain** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Module`。
形式化陈述：genWeightSpace_le_genWeightSpaceChain {k : Int} (hk : k in Ioo p q) : genW
eightSpace M (k • χ₁ + χ₂) <= genWeightSpaceChain M χ₁ χ₂ p q
参数：hk : k in Ioo p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma genWeightSpace_le_genWeightSpaceChain {k : ℤ} (hk : k ∈ Ioo p q) :
    genWeightSpace M (k • χ₁ + χ₂) ≤ genWeightSpaceChain M χ₁ χ₂ p q :=
  le_biSup (fun i ↦ genWeightSpace M (i • χ₁ + χ₂)) hk

end IsNilpotent

section LieSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

/-
**LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right** 是 Mathl
ib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilp
otent H] (hq : genWeightSpace M (q • α + χ) = ⊥) {x : L} (hx : x in rootSpace H 
α) {y : M} (hy : y in genWeightSpaceChain M α χ p q) : ⁅x, y⁆ in genWeightSpaceC
hain M α χ p q
参数：hq : genWeightSpace M (q • α + χ) = ⊥；hx : x in rootSpace H α；hy : y in genWe
ightSpaceChain M α χ p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.iSup_induction'`：iSup_induction' {ι} (N : ι -> LieSubmodule
 R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx 
: x in N i), motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.genWeightSpaceChain.eq_1`：∀ {R : Type u_1} {L : Type u_2} [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (M : Type u_3)   
[inst_3 : AddCommGroup M…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 73 条，此处仅展示前 30 条）
-/
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H α)
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by
  rw [genWeightSpaceChain, iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | mem k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) ≤ genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using! [...]` and very slow
      -- (https://github.com/leanprover-community/mathlib4/issues/19751)
      simpa only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Int.cast_one] using!
        (rootSpaceWeightSpaceProduct R L H M α (k • α + χ) ((k + 1) • α + χ)
            (by rw [add_smul]; abel) (⟨x, hx⟩ ⊗ₜ ⟨z, hz⟩)).property
    rw [genWeightSpaceChain]
    rcases eq_or_ne (k + 1) q with rfl | hk'; · simp only [hq, bot_le]
    replace hk' : k + 1 ∈ Ioo p q := ⟨by linarith [hk.1], lt_of_le_of_ne hk.2 hk'⟩
    exact le_biSup (fun k ↦ genWeightSpace M (k • α + χ)) hk'
  | zero => simp
  | add _ _ _ _ hz₁ hz₂ => rw [lie_add]; exact add_mem hz₁ hz₂
/-
**LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left** 是 Mathli
b 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpo
tent H] (hp : genWeightSpace M (p • α + χ) = ⊥) {x : L} (hx : x in rootSpace H (
-α)) {y : M} (hy : y in genWeightSpaceChain M α χ p q) : ⁅x, y⁆ in genWeightSpac
eChain M α χ p q
参数：hp : genWeightSpace M (p • α + χ) = ⊥；hx : x in rootSpace H (-α)；hy : y in ge
nWeightSpaceChain M α χ p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.genWeightSpaceChain_neg`：genWeightSpaceChain_neg : genWeightSp
aceChain M (-χ₁) χ₂ (-q) (-p) = genWeightSpaceChain M χ₁ χ₂ p q
· 使用引理 `LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right`：li
e_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
 (hq : genWeightSpace M (q • α + χ) = ⊥) {x : L} (hx : x i…
-/
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H]
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H (-α))
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

section IsCartanSubalgebra

variable [H.IsCartanSubalgebra] [IsNoetherian R L]
attribute [local instance 100] LieRing.ofAssociativeRing

/-
**LieModule.trace_toEnd_genWeightSpaceChain_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `L
ieModule`。
形式化陈述：trace_toEnd_genWeightSpaceChain_eq_zero (hp : genWeightSpace M (p • α + χ)
 = ⊥) (hq : genWeightSpace M (q • α + χ) = ⊥) {x : H} (hx : x in corootSpace α) 
: LinearMap.trace R _ (toEnd R H (genWeightSpaceChain M α χ p q) x) = 0
参数：hp : genWeightSpace M (p • α + χ) = ⊥；hq : genWeightSpace M (q • α + χ) = ⊥；h
x : x in corootSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right`：li
e_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
 (hq : genWeightSpace M (q • α + χ) = ⊥) {x : L} (hx : x i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用引理 `LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left`：lie
_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H] (
hp : genWeightSpace M (p • α + χ) = ⊥) {x : L} (hx : x in…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubmodule.coe_bracket`：coe_bracket (x : L) (m : N) : (↑⁅x, m⁆ : M) = 
⁅x, ↑m⁆
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lie_lie`：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
· 使用引理 `LinearMap.trace_lie`：trace_lie {R M : Type*} [CommRing R] [AddCommGroup 
M] [Module R M] (f g : Module.End R M) : trace R M ⁅f, g⁆ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 37 条，此处仅展示前 30 条）
-/
lemma trace_toEnd_genWeightSpaceChain_eq_zero
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ corootSpace α) :
    LinearMap.trace R _ (toEnd R H (genWeightSpaceChain M α χ p q) x) = 0 := by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(y : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M α χ p q hq hy hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    let g : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(z : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M α χ p q hp hz hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    have hfg : toEnd R H _ u = ⁅f, g⁆ := by
      ext
      rw [toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, ← hyz]
      simp only [lie_lie, LieHom.lie_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.End.lie_apply,
        AddSubgroupClass.coe_sub, f, g]
    simp [hfg]
  | zero => simp
  | add => simp_all
  | smul => simp_all

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a (potential) root `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
`I = corootSpace α` of `H` (informally, `I = ⁅H(α), H(-α)⁆`), we may find an
integral linear combination between `α` and any weight `χ` of a representation.

This is Proposition 4.4 from [carter2005] and is a key step in the proof that the roots of a
semisimple Lie algebra form a root system. It shows that the restriction of `α` to `I` vanishes iff
the restriction of every root to `I` vanishes (which cannot happen in a semisimple Lie algebra). -/
/-
**LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
形式化陈述：exists_forall_mem_corootSpace_smul_add_eq_zero [IsDomain R] [IsPrincipalId
ealRing R] [CharZero R] [Module.IsTorsionFree R M] [IsNoetherian R M] (hα : α !=
 0) (hχ : genWeightSpace M χ != ⊥) : exists a b : Int, 0 < b ∧ forall x in coroo
tSpace α, (a • α + b • χ) x = 0
参数：hα : α != 0；hχ : genWeightSpace M χ != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`：exists₂_genWeightSpace
_smul_add_eq_bot : existsᵉ (p < (0 : Int)) (q > (0 : Int)), genWeightSpace M (p 
• χ₁ + χ₂) = ⊥ ∧ genWeightSpace M (q •…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `LieSubmodule.instIsTorsionFreeSubtypeMem`：∀ {R : Type u} {L : Type v} {M
 : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   
[inst_3 : _root_.Module R M] […
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `LieSubmodule.iSupIndep_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] […
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用引理 `LieModule.iSupIndep_genWeightSpace`：iSupIndep_genWeightSpace : iSupIndep
 fun χ : L -> R => genWeightSpace M χ
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Given a (potential) root `α` relative to a Cartan subalgebra `H`, if we restrict
 to the ideal
`I = corootSpace α` of `H` (informally, `I = ⁅H(α), H(-α)⁆`), we may find an
integral linear combination between `α` and any weight `χ` of a representation.

This is Proposition 4.4 from [carter2005] and is a key step in the proof that th
e roots of a
semisimple Lie algebra form a root system. It shows that the restriction of `α` 
to `I` vanishes iff
the restriction of every root to `I` vanishes (which cannot happen in a semisimp
le Lie algebra).
-/
lemma exists_forall_mem_corootSpace_smul_add_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [Module.IsTorsionFree R M] [IsNoetherian R M]
    (hα : α ≠ 0) (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ a b : ℤ, 0 < b ∧ ∀ x ∈ corootSpace α, (a • α + b • χ) x = 0 := by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_genWeightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i ∈ Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ)) • i
  let b := ∑ i ∈ Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (genWeightSpace M χ) := by rwa [LieSubmodule.nontrivial_iff_ne_bot]
    refine Finset.sum_pos' (fun _ _ ↦ zero_le) ⟨0, Finset.mem_Ioo.mpr ⟨hp₀, hq₀⟩, ?_⟩
    rw [zero_smul, zero_add]
    exact finrank_pos
  refine ⟨a, b, Int.natCast_pos.mpr hb, fun x hx ↦ ?_⟩
  let N : ℤ → Submodule R M := fun k ↦ genWeightSpace M (k • α + χ)
  have h₁ : iSupIndep fun (i : Finset.Ioo p q) ↦ N i := by
    rw [LieSubmodule.iSupIndep_toSubmodule]
    refine (iSupIndep_genWeightSpace R H M).comp fun i j hij ↦ ?_
    exact SetCoe.ext <| smul_left_injective ℤ hα <| by rwa [add_left_inj] at hij
  have h₂ : ∀ i, MapsTo (toEnd R H M x) ↑(N i) ↑(N i) := fun _ _ ↦ LieSubmodule.lie_mem _
  have h₃ : genWeightSpaceChain M α χ p q = ⨆ i ∈ Finset.Ioo p q, N i := by
    simp_rw [N, genWeightSpaceChain_def', LieSubmodule.iSup_toSubmodule]
  rw [← trace_toEnd_genWeightSpaceChain_eq_zero M α χ p q hp hq hx,
    ← LieSubmodule.toEnd_restrict_eq_toEnd]
  -- The lines below illustrate the cost of treating `LieSubmodule` as both a
  -- `Submodule` and a `LieSubmodule` simultaneously.
  #adaptation_note /-- 2025-06-18 (https://github.com/leanprover/lean4/issues/8804).
    The `erw` causes a kernel timeout if there is no `subst`. -/
  subst a b N
  erw [LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ h₁ h₂ (genWeightSpaceChain M α χ p q) h₃]
  simp_rw [LieSubmodule.toEnd_restrict_eq_toEnd]
  convert_to! _ =
    ∑ k ∈ Finset.Ioo p q, (LinearMap.trace R { x // x ∈ (genWeightSpace M (k • α + χ)) })
      ((toEnd R { x // x ∈ H } { x // x ∈ genWeightSpace M (k • α + χ) }) x)
  simp_rw [trace_toEnd_genWeightSpace, Pi.add_apply, Pi.smul_apply, smul_add,
    ← smul_assoc, Finset.sum_add_distrib, ← Finset.sum_smul, natCast_zsmul]

end IsCartanSubalgebra

end LieSubalgebra

section

variable {M}
variable [LieRing.IsNilpotent L]
variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]
variable (α : L → R) (β : Weight R L M)

/-- This is the largest `n : ℕ` such that `i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
/-
**LieModule.chainTopCoeff** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：chainTopCoeff : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def chainTopCoeff : ℕ :=
  letI := Classical.propDecidable
  if hα : α = 0 then 0 else
  Nat.pred <| Nat.find (show ∃ n, genWeightSpace M (n • α + β : L → R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

/-- This is the largest `n : ℕ` such that `-i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
/-
**LieModule.chainBotCoeff** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：chainBotCoeff : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def chainBotCoeff : ℕ := chainTopCoeff (-α) β
/-
**LieModule.chainTopCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   LieModule.chainTopCoeff (-α) β = LieModule.chain
BotCoeff α β
参数：α : L → R；β : LieModule.Weight R L M；-α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma chainTopCoeff_neg : chainTopCoeff (-α) β = chainBotCoeff α β := rfl
/-
**LieModule.chainBotCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   LieModule.chainBotCoeff (-α) β = LieModule.chain
TopCoeff α β
参数：α : L → R；β : LieModule.Weight R L M；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.chainTopCoeff_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3
 : AddCommGroup M…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma chainBotCoeff_neg : chainBotCoeff (-α) β = chainTopCoeff α β := by
  rw [← chainTopCoeff_neg, neg_neg]
/-
**LieModule.chainTopCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (β : LieModu
le.Weight R L M),   LieModule.chainTopCoeff 0 β = 0
参数：β : LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] lemma chainTopCoeff_zero : chainTopCoeff 0 β = 0 := dif_pos rfl
/-
**LieModule.chainBotCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (β : LieModu
le.Weight R L M),   LieModule.chainBotCoeff 0 β = 0
参数：β : LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
@[simp] lemma chainBotCoeff_zero : chainBotCoeff 0 β = 0 := dif_pos neg_zero

section
variable (hα : α ≠ 0)
include hα

/-
**LieModule.chainTopCoeff_add_one** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：chainTopCoeff_add_one : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `LieModule.eventually_genWeightSpace_smul_add_eq_bot`：eventually_genWeigh
tSpace_smul_add_eq_bot : forallᶠ (k : Nat) in Filter.atTop, genWeightSpace M (k 
• χ₁ + χ₂) = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.chainTopCoeff.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma chainTopCoeff_add_one :
    letI := Classical.propDecidable
    chainTopCoeff α β + 1 =
      Nat.find (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [chainTopCoeff, dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L → R) = ⊥ := by
    rw [← e]
    exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists
  exact β.genWeightSpace_ne_bot _ (by simpa only [zero_smul, zero_add] using this)
/-
**LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
形式化陈述：genWeightSpace_chainTopCoeff_add_one_nsmul_add : genWeightSpace M ((chainT
opCoeff α β + 1) • α + β : L -> R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `LieModule.eventually_genWeightSpace_smul_add_eq_bot`：eventually_genWeigh
tSpace_smul_add_eq_bot : forallᶠ (k : Nat) in Filter.atTop, genWeightSpace M (k 
• χ₁ + χ₂) = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.chainTopCoeff_add_one`：chainTopCoeff_add_one : letI
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
lemma genWeightSpace_chainTopCoeff_add_one_nsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1) • α + β : L → R) = ⊥ := by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists
/-
**LieModule.genWeightSpace_chainTopCoeff_add_one_zsmul_add** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
形式化陈述：genWeightSpace_chainTopCoeff_add_one_zsmul_add : genWeightSpace M ((chainT
opCoeff α β + 1 : Int) • α + β : L -> R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add`：genWeightSpace
_chainTopCoeff_add_one_nsmul_add : genWeightSpace M ((chainTopCoeff α β + 1) • α
 + β : L -> R) = ⊥
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma genWeightSpace_chainTopCoeff_add_one_zsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [← genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα, ← Nat.cast_smul_eq_nsmul ℤ,
    Nat.cast_add, Nat.cast_one]
/-
**LieModule.genWeightSpace_chainBotCoeff_sub_one_zsmul_sub** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
形式化陈述：genWeightSpace_chainBotCoeff_sub_one_zsmul_sub : genWeightSpace M ((-chain
BotCoeff α β - 1 : Int) • α + β : L -> R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `LieModule.chainBotCoeff.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用引理 `LieModule.genWeightSpace_chainTopCoeff_add_one_zsmul_add`：genWeightSpace
_chainTopCoeff_add_one_zsmul_add : genWeightSpace M ((chainTopCoeff α β + 1 : In
t) • α + β : L -> R) = ⊥
-/
lemma genWeightSpace_chainBotCoeff_sub_one_zsmul_sub :
    genWeightSpace M ((-chainBotCoeff α β - 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [sub_eq_add_neg, ← neg_add, neg_smul, ← smul_neg, chainBotCoeff,
    genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

end

/-
**LieModule.genWeightSpace_nsmul_add_ne_bot_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Module`。
形式化陈述：genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n <= chainTopCoeff α β) : 
genWeightSpace M (n • α + β : L -> R) != ⊥
参数：hn : n <= chainTopCoeff α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `LieModule.eventually_genWeightSpace_smul_add_eq_bot`：eventually_genWeigh
tSpace_smul_add_eq_bot : forallᶠ (k : Nat) in Filter.atTop, genWeightSpace M (k 
• χ₁ + χ₂) = ⊥
· 使用引理 `LieModule.chainTopCoeff_add_one`：chainTopCoeff_add_one : letI
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
-/
lemma genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n ≤ chainTopCoeff α β) :
    genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ_iff, Nat.succ_eq_add_one, chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn
/-
**LieModule.genWeightSpace_zsmul_add_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：genWeightSpace_zsmul_add_ne_bot {n : Int} (hn : -chainBotCoeff α β <= n) (
hn' : n <= chainTopCoeff α β) : genWeightSpace M (n • α + β : L -> R) != ⊥
参数：hn : -chainBotCoeff α β <= n；hn' : n <= chainTopCoeff α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `LieModule.genWeightSpace_nsmul_add_ne_bot_of_le`：genWeightSpace_nsmul_ad
d_ne_bot_of_le {n} (hn : n <= chainTopCoeff α β) : genWeightSpace M (n • α + β :
 L -> R) != ⊥
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma genWeightSpace_zsmul_add_ne_bot {n : ℤ}
    (hn : -chainBotCoeff α β ≤ n) (hn' : n ≤ chainTopCoeff α β) :
      genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul, ← smul_neg, Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_nsmul_add_ne_bot_of_le (-α) β hn
/-
**LieModule.genWeightSpace_neg_zsmul_add_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieMo
dule`。
形式化陈述：genWeightSpace_neg_zsmul_add_ne_bot {n : Nat} (hn : n <= chainBotCoeff α β
) : genWeightSpace M ((-n : Int) • α + β : L -> R) != ⊥
参数：hn : n <= chainBotCoeff α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.genWeightSpace_zsmul_add_ne_bot`：genWeightSpace_zsmul_add_ne_b
ot {n : Int} (hn : -chainBotCoeff α β <= n) (hn' : n <= chainTopCoeff α β) : gen
WeightSpace M (n • α + β : L ->…
-/
lemma genWeightSpace_neg_zsmul_add_ne_bot {n : ℕ} (hn : n ≤ chainBotCoeff α β) :
    genWeightSpace M ((-n : ℤ) • α + β : L → R) ≠ ⊥ := by
  apply genWeightSpace_zsmul_add_ne_bot α β <;> lia

/-- The last weight in an `α`-chain through `β`. -/
noncomputable
/-
**LieModule.chainTop** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：chainTop (α : L -> R) (β : Weight R L M) : Weight R L M
参数：α : L -> R；β : Weight R L M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def chainTop (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

/-- The first weight in an `α`-chain through `β`. -/
noncomputable
/-
**LieModule.chainBot** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：chainBot (α : L -> R) (β : Weight R L M) : Weight R L M
参数：α : L -> R；β : Weight R L M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def chainBot (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨(- chainBotCoeff α β : ℤ) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩
/-
**LieModule.coe_chainTop'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：coe_chainTop' : (chainTop α β : L -> R) = chainTopCoeff α β • α + β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_chainTop' : (chainTop α β : L → R) = chainTopCoeff α β • α + β := rfl
/-
**LieModule.coe_chainTop** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   ⇑(LieModule.chainTop α β) = ↑(LieModule.chainTop
Coeff α β) • α + ⇑β
参数：α : L → R；β : LieModule.Weight R L M；LieModule.chainTop α β；LieModule.chainTo
pCoeff α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
-/
@[simp] lemma coe_chainTop : (chainTop α β : L → R) = (chainTopCoeff α β : ℤ) • α + β := by
  rw [Nat.cast_smul_eq_nsmul ℤ]; rfl
/-
**LieModule.coe_chainBot** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   ⇑(LieModule.chainBot α β) = -↑(LieModule.chainBo
tCoeff α β) • α + ⇑β
参数：α : L → R；β : LieModule.Weight R L M；LieModule.chainBot α β；LieModule.chainBo
tCoeff α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_chainBot : (chainBot α β : L → R) = (-chainBotCoeff α β : ℤ) • α + β := rfl
/-
**LieModule.chainTop_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   LieModule.chainTop (-α) β = LieModule.chainBot α
 β
参数：α : L → R；β : LieModule.Weight R L M；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma chainTop_neg : chainTop (-α) β = chainBot α β := by ext; simp
/-
**LieModule.chainBot_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (α : L → R) 
(β : LieModule.Weight R L M),   LieModule.chainBot (-α) β = LieModule.chainTop α
 β
参数：α : L → R；β : LieModule.Weight R L M；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.chainBotCoeff_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3
 : AddCommGroup M…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma chainBot_neg : chainBot (-α) β = chainTop α β := by ext; simp
/-
**LieModule.chainTop_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (β : LieModu
le.Weight R L M),   LieModule.chainTop 0 β = β
参数：β : LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `LieModule.chainTopCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma chainTop_zero : chainTop 0 β = β := by ext; simp
/-
**LieModule.chainBot_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : IsAddTorsionFree R] [inst_9 : IsDomain R] 
  [inst_10 : Module.IsTorsionFree R M] [inst_11 : IsNoetherian R M] (β : LieModu
le.Weight R L M),   LieModule.chainBot 0 β = β
参数：β : LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.chainBotCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma chainBot_zero : chainBot 0 β = β := by ext; simp

section
variable (hα : α ≠ 0)
include hα

/-
**LieModule.genWeightSpace_add_chainTop** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：genWeightSpace_add_chainTop : genWeightSpace M (α + chainTop α β : L -> R)
 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.coe_chainTop'`：coe_chainTop' : (chainTop α β : L -> R) = chain
TopCoeff α β • α + β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
· 使用引理 `LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add`：genWeightSpace
_chainTopCoeff_add_one_nsmul_add : genWeightSpace M ((chainTopCoeff α β + 1) • α
 + β : L -> R) = ⊥
-/
lemma genWeightSpace_add_chainTop :
    genWeightSpace M (α + chainTop α β : L → R) = ⊥ := by
  rw [coe_chainTop', ← add_assoc, ← succ_nsmul',
    genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]
/-
**LieModule.genWeightSpace_neg_add_chainBot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：genWeightSpace_neg_add_chainBot : genWeightSpace M (-α + chainBot α β : L 
-> R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.chainTop_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用引理 `LieModule.genWeightSpace_add_chainTop`：genWeightSpace_add_chainTop : gen
WeightSpace M (α + chainTop α β : L -> R) = ⊥
-/
lemma genWeightSpace_neg_add_chainBot :
    genWeightSpace M (-α + chainBot α β : L → R) = ⊥ := by
  rw [← chainTop_neg, genWeightSpace_add_chainTop _ _ (by simpa using hα)]
/-
**LieModule.chainTop_isNonZero'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：chainTop_isNonZero' (hα' : genWeightSpace M α != ⊥) : (chainTop α β).IsNon
Zero
参数：hα' : genWeightSpace M α != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `LieModule.genWeightSpace_add_chainTop`：genWeightSpace_add_chainTop : gen
WeightSpace M (α + chainTop α β : L -> R) = ⊥
-/
lemma chainTop_isNonZero' (hα' : genWeightSpace M α ≠ ⊥) :
    (chainTop α β).IsNonZero := by
  by_contra e
  apply hα'
  rw [← add_zero (α : L → R), ← e, genWeightSpace_add_chainTop _ _ hα]

end

/-
**LieModule.chainTop_isNonZero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) : (chainTop α β
).IsNonZero
参数：α β : Weight R L M；hα : α.IsNonZero。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.chainTop_isNonZero'`：chainTop_isNonZero' (hα' : genWeightSpace
 M α != ⊥) : (chainTop α β).IsNonZero
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…
-/
lemma chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) :
    (chainTop α β).IsNonZero :=
  chainTop_isNonZero' α β hα α.2

end

end LieModule

section Field

open LieAlgebra LieModule

variable {K : Type*} [Field K] [CharZero K] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [Module K M] [LieModule K L M]
  [IsTriangularizable K H M] [FiniteDimensional K M]

/-
**LieModule.isNilpotent_toEnd_of_mem_rootSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.isNilpotent_toEnd_of_mem_rootSpace {x : L} {χ : H -> K} (hχ : χ 
!= 0) (hx : x in rootSpace H χ) : _root_.IsNilpotent (toEnd K L M x)
参数：hχ : χ != 0；hx : x in rootSpace H χ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.isNilpotent_iff_of_finite`：Module.End.isNilpotent_iff_of_fini
te [Module.Finite R M] {f : End R M} : IsNilpotent f ↔ forall m : M, exists n : 
Nat, (f ^ n) m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top'`：iSup_genWeightSpace_eq_top' [IsTr
iangularizable K L M] : ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤
· 使用定理 `LieSubmodule.iSup_induction'`：iSup_induction' {ι} (N : ι -> LieSubmodule
 R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx 
: x in N i), motiv…
· 使用引理 `LieModule.exists_genWeightSpace_smul_add_eq_bot`：exists_genWeightSpace_s
mul_add_eq_bot : exists k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用引理 `LieAlgebra.toEnd_pow_apply_mem`：toEnd_pow_apply_mem {χ₁ χ₂ : H -> R} {x 
: L} {m : M} (hx : x in rootSpace H χ₁) (hm : m in genWeightSpace M χ₂) (n) : (t
oEnd R L M x ^ n : M…
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Module.End.pow_map_zero_of_le`：pow_map_zero_of_le {f : End R M} {m : M} 
{k l : Nat} (hk : k <= l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma LieModule.isNilpotent_toEnd_of_mem_rootSpace
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (toEnd K L M x) := by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun m ↦ ?_
  have hm : m ∈ ⨆ χ : LieModule.Weight K H M, genWeightSpace M χ := by
    simp [iSup_genWeightSpace_eq_top' K H M]
  induction hm using LieSubmodule.iSup_induction' with
  | zero => exact ⟨0, map_zero _⟩
  | mem χ₂ m₂ hm₂ =>
    obtain ⟨n, -, hn⟩ := exists_genWeightSpace_smul_add_eq_bot M χ χ₂ hχ
    use n
    have := toEnd_pow_apply_mem hx hm₂ n
    rwa [hn, LieSubmodule.mem_bot] at this
  | add m₁ m₂ hm₁ hm₂ hm₁' hm₂' =>
    obtain ⟨n₁, hn₁⟩ := hm₁'
    obtain ⟨n₂, hn₂⟩ := hm₂'
    refine ⟨max n₁ n₂, ?_⟩
    rw [map_add, Module.End.pow_map_zero_of_le le_sup_left hn₁,
      Module.End.pow_map_zero_of_le le_sup_right hn₂, add_zero]
/-
**LieAlgebra.isNilpotent_ad_of_mem_rootSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieAlgebra.isNilpotent_ad_of_mem_rootSpace [IsTriangularizable K H L] [Fin
iteDimensional K L] {x : L} {χ : H -> K} (hχ : χ != 0) (hx : x in rootSpace H χ)
 : _root_.IsNilpotent (ad K L x)
参数：hχ : χ != 0；hx : x in rootSpace H χ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.isNilpotent_toEnd_of_mem_rootSpace`：LieModule.isNilpotent_toEn
d_of_mem_rootSpace {x : L} {χ : H -> K} (hχ : χ != 0) (hx : x in rootSpace H χ) 
: _root_.IsNilpotent (toEnd K L M …
-/
lemma LieAlgebra.isNilpotent_ad_of_mem_rootSpace
    [IsTriangularizable K H L] [FiniteDimensional K L]
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (ad K L x) :=
  isNilpotent_toEnd_of_mem_rootSpace (M := L) H hχ hx

end Field

