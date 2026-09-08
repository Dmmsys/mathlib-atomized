/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Indecomposable
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Existence of bases for crystallographic root systems

## Main results:
* `RootPairing.Base.mk'`: an alternate constructor for `RootPairing.Base` which demands the axioms
  for roots but not for coroots.
* `RootPairing.nonempty_base`: base existence proof for reduced crystallographic root systems.

## Implementation details

The proof needs a set of ordered coefficients, even though the ultimate existence statement does
not. There are at least two ways to deal with this:
(a) Using the fact that a crystallographic root system induces a `ℚ`-structure, pass to the root
    system over `ℚ` defined by `RootPairing.restrictScalarsRat`, and develop a theory of base
    change for root system bases.
(b) Introduce a second set of ordered coefficients (ultimately taken to be `ℚ`) and develop a
    theory with two sets of coefficients simultaneously in play.

It is not really clear which is the better approach but here we opt for approach (b) as it seems
to yield slightly more general results.

-/

@[expose] public section

open Function IsAddIndecomposable Module Set Submodule

namespace RootPairing

variable {ι R M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  {S : Type*} [LinearOrder S] [AddCommGroup S] [IsOrderedAddMonoid S] (f : M →+ S)

/-- This is [serre1965](Ch. V, §9, Lemma 3). -/
/-
**RootPairing.baseOf_pairwise_pairing_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：baseOf_pairwise_pairing_le_zero [CharZero R] [IsDomain R] [P.IsCrystallogr
aphic] (hf : forall i, f (P.root i) != 0) : (baseOf P.root f).Pairwise fun i j =
> P.pairingIn Int i j <= 0
参数：hf : forall i, f (P.root i) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddIndecomposable.pairwise_baseOf_sub_notMem`：∀ {ι : Type u_1} {G : Ty
pe u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S]   [inst_
2 : InvolutiveNeg ι] [inst_3 : AddCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `RootPairing.root_sub_root_mem_of_pairingIn_pos`：root_sub_root_mem_of_pai
ringIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) : α i - α j in Φ

--- 原说明 ---
This is [serre1965](Ch. V, §9, Lemma 3).
-/
lemma baseOf_pairwise_pairing_le_zero [CharZero R] [IsDomain R] [P.IsCrystallographic]
    (hf : ∀ i, f (P.root i) ≠ 0) :
    (baseOf P.root f).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0 := by
  let _i := P.indexNeg
  intro i hi j hj hne
  have := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root (by simp) f hf hi hj hne
  contrapose! this
  exact P.root_sub_root_mem_of_pairingIn_pos this hne

/-- This lemma is usually established for root systems with coefficients `R` equal to `ℚ` or `ℝ`, in
which case one may take `S = R`. However our statement allows for more general coefficients such as
`R = ℂ` and `S = ℚ`.

This lemma is mostly a stepping stone en route to `RootPairing.linearIndepOn_root_baseOf` (where
linear independence is established over `R` rather than just `S`) except that this version does not
make the field assumption and so covers the case `S = R = ℤ` which the latter does not. -/
/-
**RootPairing.linearIndepOn_root_baseOf'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`
。
形式化陈述：linearIndepOn_root_baseOf' [IsDomain R] {S : Type*} [LinearOrder S] [CommR
ing S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R] [Module S M] [Is
ScalarTower S R M] [Module S N] [IsScalarTower S R N] [P.IsValuedIn S] [P.IsCrys
tallographic] (f : Dual S M) (hf : forall i, f (P.root i) != 0) : LinearIndepOn 
S P.root (baseOf P.root (f : M ->+ S))
参数：f : Dual S M；hf : forall i, f (P.root i) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.charZero_of_charZero`：Algebra.charZero_of_charZero [CharZero R] 
: CharZero A
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.posRootForm_eq`：posRootForm_eq : (P.posRootForm S).posForm =
 P.RootFormIn S
· 使用引理 `RootPairing.posRootForm_rootFormIn_posDef`：posRootForm_rootFormIn_posDef
 : (P.RootFormIn S).toQuadraticMap.PosDef
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `RootPairing.RootPositiveForm.posForm_apply_root_root_le_zero_iff`：posFor
m_apply_root_root_le_zero_iff [IsStrictOrderedRing S] (hi : P.root i in span S (
range P.root)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.algebraMap_pairingIn'`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `RootPairing.baseOf_pairwise_pairing_le_zero`：baseOf_pairwise_pairing_le_
zero [CharZero R] [IsDomain R] [P.IsCrystallographic] (hf : forall i, f (P.root 
i) != 0) : (baseOf P.root f).Pair…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero`：LinearMap.Bil
inForm.linearIndependent_of_pairwise_le_zero {ι R M : Type*} [CommRing R] [Linea
rOrder R] [IsStrictOrderedRing R] [AddCommGroup…
· 使用定理 `LinearMap.linearIndependent_iff_of_disjoint`：∀ {ι : Type u'} {R : Type u
_2} {M : Type u_4} {M' : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup M'] [inst_3…
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥

--- 原说明 ---
This lemma is usually established for root systems with coefficients `R` equal t
o `ℚ` or `ℝ`, in
which case one may take `S = R`. However our statement allows for more general c
oefficients such as
`R = ℂ` and `S = ℚ`.

This lemma is mostly a stepping stone en route to `RootPairing.linearIndepOn_roo
t_baseOf` (where
linear independence is established over `R` rather than just `S`) except that th
is version does not
make the field assumption and so covers the case `S = R = ℤ` which the latter do
es not.
-/
lemma linearIndepOn_root_baseOf' [IsDomain R] {S : Type*}
    [LinearOrder S] [CommRing S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]
    [P.IsValuedIn S] [P.IsCrystallographic]
    (f : Dual S M) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn S P.root (baseOf P.root (f : M →+ S)) := by
  have : CharZero R := Algebra.charZero_of_charZero S R
  have : Fintype ι := Fintype.ofFinite ι
  let M₀ := span S (range P.root)
  let v (i : baseOf P.root (f : M →+ S)) : M₀ := P.rootSpanMem S i
  change LinearIndependent S (M₀.subtype ∘ v)
  suffices LinearIndependent S v by
    rwa [LinearMap.linearIndependent_iff_of_disjoint M₀.subtype (by simp)]
  let f' : Dual S M₀ := f ∘ₗ M₀.subtype
  obtain ⟨B, hB⟩ : ∃ B : P.RootPositiveForm S, B.posForm.toQuadraticMap.PosDef :=
    ⟨P.posRootForm S, by simpa using P.posRootForm_rootFormIn_posDef S⟩
  have hp (i : baseOf P.root (f : M →+ S)) : 0 < f' (v i) := by obtain ⟨i, -, hi⟩ := i; simpa
  have hn : Pairwise fun (i j : baseOf P.root (f : M →+ S)) ↦ B.posForm (v i) (v j) ≤ 0 := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    rw [B.posForm_apply_root_root_le_zero_iff, ← P.algebraMap_pairingIn' S ℤ]
    simpa using P.baseOf_pairwise_pairing_le_zero _ hf (by simpa) (by simpa) (by aesop : i ≠ j)
  exact LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero B.posForm hB f' v hp hn
/-
**RootPairing.ncard_eq_finrank_of_linearIndepOn_of** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：ncard_eq_finrank_of_linearIndepOn_of [P.IsRootSystem] [Nontrivial R] {s : 
Set ι} (hli : LinearIndepOn R P.root s) (hsp : forall i, P.root i in AddSubmonoi
d.closure (P.root '' s) ∨ -P.root i in AddSubmonoid.closure (P.root '' s)) : s.n
card = finrank R M
参数：hli : LinearIndepOn R P.root s；hsp : forall i, P.root i in AddSubmonoid.closu
re (P.root '' s) ∨ -P.root i in AddSubmonoid.closure (P.root '' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_int_eq_addSubgroupClosure`：span_int_eq_addSubgroupClosure
 {M : Type*} [AddCommGroup M] (s : Set M) : (span Int s).toAddSubgroup = AddSubg
roup.closure s
· 使用定理 `AddSubgroup.le_closure_toAddSubmonoid`：∀ {G : Type u_1} [inst : AddGroup
 G] (S : Set G), AddSubmonoid.closure S ≤ (AddSubgroup.closure S).toAddSubmonoid
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
lemma ncard_eq_finrank_of_linearIndepOn_of [P.IsRootSystem] [Nontrivial R]
    {s : Set ι}
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    s.ncard = finrank R M := by
  let b : Basis s R M := Basis.mk hli <| by
    rw [← IsRootSystem.span_root_eq_top (P := P), span_le, ← span_span_of_tower (R := ℤ)]
    rintro - ⟨i, rfl⟩
    apply subset_span
    rcases hsp i with hi | hi <;>
      simpa [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, span_int_eq_addSubgroupClosure,
        ← image_eq_range] using AddSubgroup.le_closure_toAddSubmonoid (P.root '' s) hi
  have _i : Fintype s := Fintype.ofFinite s
  rw [ncard_eq_toFinset_card]
  simpa using (finrank_eq_card_basis b).symm

end CommRing

section Field

variable [Field R] [CharZero R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsRootSystem] [P.IsCrystallographic]

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.linearIndepOn_root_baseOf** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：linearIndepOn_root_baseOf (f : M ->+ Rat) (hf : forall i, f (P.root i) != 
0) : LinearIndepOn R P.root (baseOf P.root f)
参数：f : M ->+ Rat；hf : forall i, f (P.root i) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Submodule.coe_toAddSubgroup`：coe_toAddSubgroup : (p.toAddSubgroup : Set 
M) = p
· 使用定理 `Submodule.span_int_eq_addSubgroupClosure`：span_int_eq_addSubgroupClosure
 {M : Type*} [AddCommGroup M] (s : Set M) : (span Int s).toAddSubgroup = AddSubg
roup.closure s
· 使用定理 `AddSubgroup.closure_image_isAddIndecomposable_baseOf`：∀ {ι : Type u_1} {
G : Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S] [F
inite ι]   [inst_3 : InvolutiveNeg ι] [ins…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `AddSubgroup.subset_closure`：∀ {G : Type u_1} [inst : AddGroup G] {k : Se
t G}, k ⊆ ↑(AddSubgroup.closure k)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
（共 63 条，此处仅展示前 30 条）
-/
lemma linearIndepOn_root_baseOf (f : M →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn R P.root (baseOf P.root f) := by
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  let := P.indexNeg
  have : Fintype (baseOf P.root f) := Fintype.ofFinite _
  let v (i : baseOf P.root f) : P.rootSpan ℚ := P.rootSpanMem ℚ i
  change LinearIndependent R ((P.rootSpan ℚ).subtype ∘ v)
  have h_span : span ℚ (range v) = ⊤ := by
    suffices span ℚ (range v) = span ℚ (range (P.rootSpanMem ℚ)) by
      rw [this, eq_top_iff, ← (P.rootSpan ℚ).subtype.map_le_map_iff' (by simp), map_span,
        ← image_univ, ← image_comp]
      simp
    apply le_antisymm (span_mono fun x i ↦ by aesop) (span_le.mpr ?_)
    rintro - ⟨i, rfl⟩
    suffices (P.rootSpanMem ℚ i : M) ∈ span ℚ (P.root '' baseOf P.root f) by
      rw [← (injective_subtype (P.rootSpan ℚ)).mem_set_image, ← map_coe, SetLike.mem_coe, map_span,
        ← image_univ, ← image_comp]
      convert! this
      aesop
    rw [← span_span_of_tower ℤ, ← Submodule.coe_toAddSubgroup, span_int_eq_addSubgroupClosure,
      AddSubgroup.closure_image_isAddIndecomposable_baseOf P.root (by simp) f (by simpa)]
    exact subset_span <| AddSubgroup.subset_closure <| by simp
  have h_card : Nat.card (baseOf P.root f) = finrank R M := by
    let b : Basis (baseOf P.root f) ℚ (P.rootSpan ℚ) := by
      replace this : LinearIndependent ℚ v :=
        .of_comp (P.rootSpan ℚ).subtype <| P.linearIndepOn_root_baseOf' f.toRatLinearMap hf
      exact Basis.mk this (by rw [h_span])
    rw [← RootPairing.finrank_rootSpanIn ℚ P, finrank_eq_nat_card_basis b]
  replace h_span : span R (range <| (P.rootSpan ℚ).subtype ∘ v) = ⊤ := by
    rw [range_comp, ← span_span_of_tower ℚ, span_image, h_span]
    simp
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, h_span, finrank_top, ← h_card,
    Fintype.card_eq_nat_card]
/-
**RootPairing.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing`。
形式化陈述：eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure (s : Set ι) (hli : Li
nearIndepOn R P.root s) (hsp : forall i, P.root i in AddSubmonoid.closure (P.roo
t '' s) ∨ -P.root i in AddSubmonoid.closure (P.root '' s)) (f : M ->+ Rat) (hf :
 forall i in s, f (P.root i) = 1) : s = baseOf P.root f
参数：s : Set ι；hli : LinearIndepOn R P.root s；hsp : forall i, P.root i in AddSubmo
noid.closure (P.root '' s) ∨ -P.root i in AddSubmonoid.closure (P.root '' s)；f :
 M ->+ Rat；hf : forall i in s, f (P.root i) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure`：∀ {ι : Type u_1} {
G : Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S]   
[inst_2 : InvolutiveNeg ι] [inst_3 : AddCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsAddIndecomposable.mem_or_neg_mem_closure_baseOf`：∀ {ι : Type u_1} {G :
 Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S] [Fini
te ι]   [inst_3 : InvolutiveNeg ι] [ins…
· 使用引理 `RootPairing.ncard_eq_finrank_of_linearIndepOn_of`：ncard_eq_finrank_of_li
nearIndepOn_of [P.IsRootSystem] [Nontrivial R] {s : Set ι} (hli : LinearIndepOn 
R P.root s) (hsp : forall i, P.root i …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `RootPairing.linearIndepOn_root_baseOf`：linearIndepOn_root_baseOf (f : M 
->+ Rat) (hf : forall i, f (P.root i) != 0) : LinearIndepOn R P.root (baseOf P.r
oot f)
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
（共 33 条，此处仅展示前 30 条）
-/
lemma eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure
    (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s))
    (f : M →+ ℚ) (hf : ∀ i ∈ s, f (P.root i) = 1) :
    s = baseOf P.root f := by
  let _i := P.indexNeg
  have h_card : (baseOf P.root f).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) ≠ 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root f s (by aesop) i (P.ne_zero i) (by simp) (hsp i)
    have aux (i : ι) := mem_or_neg_mem_closure_baseOf P.root f i (hf' i) (by simp)
    rw [P.ncard_eq_finrank_of_linearIndepOn_of hli hsp, P.ncard_eq_finrank_of_linearIndepOn_of
      (P.linearIndepOn_root_baseOf f hf') aux]
  suffices s ⊆ baseOf P.root f from eq_of_subset_of_ncard_le this (by rw [h_card])
  replace hsp (i : ι) : ∃ z : ℤ, f (P.root i) = z := by
    rcases hsp i with hi | hi
    · exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
    · suffices ∃ z : ℤ, f (P.root (-i)) = z by obtain ⟨z, hz⟩ := this; exact ⟨-z, by simp [← hz]⟩
      replace hi : P.root (-i) ∈ AddSubmonoid.closure (P.root '' s) := by simpa
      exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
  refine fun i hi ↦ ⟨by aesop, fun j hj k hk contra ↦ ?_⟩
  obtain ⟨n, hn⟩ := hsp j
  obtain ⟨m, hm⟩ := hsp k
  replace hj : 0 < n := by simpa [hn] using hj
  replace hk : 0 < m := by simpa [hm] using hk
  replace contra : 1 = n + m := by
    replace contra := congr(f $contra)
    rwa [hf i hi, map_add, hn, hm, ← Int.cast_add, ← Int.cast_one, Int.cast_inj] at contra
  lia
/-
**RootPairing.eq_baseOf_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：eq_baseOf_iff (s : Set ι) (f : M ->+ Rat) (hf : forall i in s, f (P.root i
) = 1) (hf' : forall i, f (P.root i) != 0) : s = baseOf P.root f ↔ LinearIndepOn
 R P.root s ∧ forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨ -P.root
 i in AddSubmonoid.closure (P.root '' s)
参数：s : Set ι；f : M ->+ Rat；hf : forall i in s, f (P.root i) = 1；hf' : forall i, 
f (P.root i) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.linearIndepOn_root_baseOf`：linearIndepOn_root_baseOf (f : M 
->+ Rat) (hf : forall i, f (P.root i) != 0) : LinearIndepOn R P.root (baseOf P.r
oot f)
· 使用定理 `IsAddIndecomposable.mem_or_neg_mem_closure_baseOf`：∀ {ι : Type u_1} {G :
 Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S] [Fini
te ι]   [inst_3 : InvolutiveNeg ι] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure`：eq_bas
eOf_of_linearIndepOn_of_mem_or_neg_mem_closure (s : Set ι) (hli : LinearIndepOn 
R P.root s) (hsp : forall i, P.root i in AddSubmonoid.…
-/
lemma eq_baseOf_iff (s : Set ι) (f : M →+ ℚ)
    (hf : ∀ i ∈ s, f (P.root i) = 1) (hf' : ∀ i, f (P.root i) ≠ 0) :
    s = baseOf P.root f ↔
      LinearIndepOn R P.root s ∧
        ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
            -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
  let := P.indexNeg
  refine ⟨?_, fun ⟨hli, sp⟩ ↦ P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli sp f hf⟩
  rintro rfl
  exact ⟨P.linearIndepOn_root_baseOf f hf', fun i ↦
    mem_or_neg_mem_closure_baseOf P.root f i (by simp_all) (by simp)⟩

variable [P.IsReduced]
/-
**RootPairing.baseOf_root_eq_baseOf_coroot_aux** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma baseOf_root_eq_baseOf_coroot_aux
    (f : M →+ ℚ) (g : N →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f ⊆ baseOf P.coroot (g : N →+ ℚ) := by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let s := baseOf P.root f
  refine fun i hi ↦ ⟨by obtain ⟨hi, -⟩ := hi; aesop, fun j hj k hk contra ↦ ?_⟩
  suffices i = j by grind
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ᵉ (u > (0 : ℚ)) (v > (0 : ℚ)),
      P.root i = u • P.root j + v • P.root k := by
    let l (i : ι) := P.RootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i)
    have hl (i : ι) : 0 < l i := by
      simpa only [l, ← posRootForm_eq] using RootPositiveForm.zero_lt_posForm_apply_root _ _
    refine ⟨l i / l j, by simp [hl], l i / l k, by simp [hl], ?_⟩
    simp only [P.coroot_eq_polarizationEquiv_apply_root, ← map_smul, ← map_add,
      P.PolarizationEquiv.injective.eq_iff] at contra
    let l' (i : ι) := P.RootForm (P.root i) (P.root i)
    have hll' (i : ι) : l i = l' i := P.algebraMap_rootFormIn ℚ _ _
    change (2 / l' i) • P.root i = (2 / l' j) • P.root j + (2 / l' k) • P.root k at contra
    replace contra := congr_arg ((2 / l' i)⁻¹ • ·) contra
    have aux₁ : 2 / l' i ≠ 0 := by simpa using IsAnisotropic.rootForm_root_ne_zero i
    have aux₂ (j : ι) : (2 / l' i)⁻¹ * (2 / l' j) = l i / l j := by ring_nf; simp [hll']
    simp only [smul_add, smul_smul, inv_mul_cancel₀ aux₁, aux₂, one_smul] at contra
    rw [contra]
    module
  have hjk {l : ι} (hl : 0 < g (P.coroot l)) :
      ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : M) = P.root l := by
    rwa [← Submodule.mem_span_iff_of_fintype, ← mem_toAddSubmonoid, span_nat_eq_addSubmonoidClosure,
      AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
      AddSubmonoid.mem_closure_image_pos_iff P.root f _ (P.ne_zero _), hfg]
  obtain ⟨a, ha⟩ : ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : M) = P.root j := hjk hj
  obtain ⟨b, hb⟩ : ∃ d : P.root '' s → ℕ, ∑ x, d x • (x : M) = P.root k := hjk hk
  let ri : P.root '' s := ⟨P.root i, mem_image_of_mem _ hi⟩
  replace huv : u • (Nat.cast ∘ a) + v • (Nat.cast (R := ℚ) ∘ b) = Pi.single ri 1 := by
    simp_rw [← ha, ← hb, Finset.smul_sum, ← Finset.sum_add_distrib, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, ← add_smul] at huv
    have aux : P.root i = ∑ x, Pi.single (M := fun x : P.root '' s ↦ ℚ) ri 1 x • (x : M) := by
      simp [ri]
    rw [eq_comm, aux] at huv
    have hli : LinearIndepOn ℚ id (P.root '' s) := by
      rw [← linearIndepOn_iff_image P.root.injective.injOn]
      exact (linearIndepOn_root_baseOf P f hf).restrict_scalars' ℚ
    rw [← linearIndependent_subtype_iff] at hli
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hli huv
  obtain ⟨q, hq, hq'⟩ : ∃ q > (0 : ℚ), P.root j = q • P.root i := by
    suffices P.root j = (a ri : ℚ) • P.root i by
      refine ⟨a ri, ?_, this⟩
      by_contra contra
      replace contra : a ri = 0 := by simpa using contra
      simp [contra, P.ne_zero j] at this
    have (x : P.root '' s) (hx : x ≠ ri) : a x = 0 := by
      replace huv : u * ↑(a x) + v * ↑(b x) = 0 := by simpa [hx] using congr($huv x)
      suffices u * (a x) = 0 by simpa [hu.ne'] using this
      have : 0 ≤ u * (a x) := by positivity
      have : 0 ≤ v * (b x) := by positivity
      grind
    replace this (x : P.root '' s) (hx : a x • (x : M) ≠ 0) :  x ∈ ({ri} : Finset _) := by
      rw [Finset.mem_singleton]
      by_contra! contra
      simp [this x contra] at hx
    simp [← ha, ← Fintype.sum_subset this, ri, Nat.cast_smul_eq_nsmul]
  have hij : ¬ LinearIndependent R ![P.root i, P.root j] := by
    simp_rw [LinearIndependent.pair_iff, not_forall]
    exact ⟨q, -1, by simp [Rat.cast_smul_eq_qsmul, hq'], by simp⟩
  rcases IsReduced.eq_or_eq_neg i j hij with hij | hij
  · simpa using hij
  · grind
/-
**RootPairing.baseOf_root_eq_baseOf_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：baseOf_root_eq_baseOf_coroot (f : M ->+ Rat) (hf : forall i, f (P.root i) 
!= 0) (g : N ->+ Rat) (hg : forall i, g (P.coroot i) != 0) (hfg : forall i, 0 < 
f (P.root i) ↔ 0 < g (P.coroot i)) : baseOf P.root f = baseOf P.coroot (g : N ->
+ Rat)
参数：f : M ->+ Rat；hf : forall i, f (P.root i) != 0；g : N ->+ Rat；hg : forall i, g
 (P.coroot i) != 0；hfg : forall i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.BaseExists.0.RootPairing.baseO
f_root_eq_baseOf_coroot_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} [Finite ι] [inst : AddCommGroup M]   [inst_1 : AddCommGroup N] [inst_
2 : Field…
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RootPairing.flip_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Mo
dule R M] […
· 使用定理 `RootPairing.flip_coroot`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} 
{N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.
Module R M] […
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma baseOf_root_eq_baseOf_coroot
    (f : M →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0)
    (g : N →+ ℚ) (hg : ∀ i, g (P.coroot i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f = baseOf P.coroot (g : N →+ ℚ) :=
  subset_antisymm (P.baseOf_root_eq_baseOf_coroot_aux f g hf hfg)
    (P.flip.baseOf_root_eq_baseOf_coroot_aux g f hg (by aesop))

/-- This is really just an auxiliary result en route to `RootPairing.Base.mk'`. -/
/-
**RootPairing.coroot_mem_or_neg_mem_closure_of_root** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing`。
形式化陈述：coroot_mem_or_neg_mem_closure_of_root (s : Set ι) (hli : LinearIndepOn R P
.root s) (hsp : forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨ -P.ro
ot i in AddSubmonoid.closure (P.root '' s)) (i : ι) : P.coroot i in AddSubmonoid
.closure (P.coroot '' s) ∨ -P.coroot i in AddSubmonoid.closure (P.coroot '' s)
参数：s : Set ι；hli : LinearIndepOn R P.root s；hsp : forall i, P.root i in AddSubmo
noid.closure (P.root '' s) ∨ -P.root i in AddSubmonoid.closure (P.root '' s)；i :
 ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.exists_dual_forall_apply_eq_one`：Module.exists_dual_forall_apply_
eq_one {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] {s : Set ι} {v : 
ι -> V} (hli : LinearIndepOn…
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `RootPairing.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure`：eq_bas
eOf_of_linearIndepOn_of_mem_or_neg_mem_closure (s : Set ι) (hli : LinearIndepOn 
R P.root s) (hsp : forall i, P.root i in AddSubmonoid.…
· 使用定理 `AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure`：∀ {ι : Type u_1} {
G : Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S]   
[inst_2 : InvolutiveNeg ι] [inst_3 : AddCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.instIsValuedInRatOfIsCrystallographic`：∀ {ι : Type u_1} {R :
 Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGr
oup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
This is really just an auxiliary result en route to `RootPairing.Base.mk'`.
-/
lemma coroot_mem_or_neg_mem_closure_of_root (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s))
    (i : ι) :
     P.coroot i ∈ AddSubmonoid.closure (P.coroot '' s) ∨
    -P.coroot i ∈ AddSubmonoid.closure (P.coroot '' s) := by
  let _i := P.indexNeg
  let _i : Fintype ι := Fintype.ofFinite ι
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  obtain ⟨f, hf'⟩ := exists_dual_forall_apply_eq_one (hli.restrict_scalars' ℚ)
  have hf := P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli hsp f hf'
  have hf₀ (i : ι) : f (P.root i) ≠ 0 :=
    AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure P.root (f : M →+ ℚ) s (by simp_all) i
      (P.ne_zero i) (by simp) (hsp i)
  have aux (i : ι) : ∃ q : ℚ, 0 < q ∧ q = 2 / P.RootForm (P.root i) (P.root i) := by
    refine ⟨2 / P.RootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i), ?_, ?_⟩
    · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, ← posRootForm_eq]
      exact (P.posRootForm ℚ).zero_lt_posForm_apply_root i (P.rootSpanMem ℚ i).property
    · simp [← P.algebraMap_rootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i)]
  let g : Dual ℚ N := f ∘ₗ (P.PolarizationEquiv.symm.restrictScalars ℚ).toLinearMap
  have hg₀ (i : ι) : g (P.coroot i) ≠ 0 := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀.ne', hf₀ i]
  have hg (i : ι) : 0 < g (P.coroot i) ↔ 0 < f (P.root i) := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀]
  rw [hf, P.baseOf_root_eq_baseOf_coroot f hf₀ g hg₀ (fun i ↦ (hg i).symm)]
  exact mem_or_neg_mem_closure_baseOf P.coroot (g : N →+ ℚ) i (hg₀ i) (by simp)

/-- An alternate constructor for `RootPairing.Base` which demands the axioms for roots but not for
coroots. -/
/-
**RootPairing.Base.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [Finite ι] →           [inst : AddCommGroup M] →             [inst
_1 : AddCommGroup N] →               [inst_2 : Field R] →                 [CharZ
ero R] →                   [inst_4 : _root_.Module R M] →                     [i
nst_5 : _root_.Module R N] →                       (P : RootPairing ι R M N) →  
                       [P.IsRootSystem] →                           [P.IsCrystal
lographic] →                             [P.IsReduced] →                        
       (s : Set ι) →                                 LinearIndepOn R (⇑P.root) s
 →                                   (∀ (i : ι),                                
       P.root i ∈ AddSubmonoid.closure (⇑P.root '' s) ∨                         
                -P.root i ∈ AddSubmonoid.closure (⇑P.root '' s)) →              
                       P.Base
参数：P : RootPairing ι R M N；s : Set ι；⇑P.root；∀ (i : ι),                         
              P.root i ∈ AddSubmonoid.closure (⇑P.root '' s) ∨                  
                       -P.root i ∈ AddSubmonoid.closure (⇑P.root '' s)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate constructor for `RootPairing.Base` which demands the axioms for roo
ts but not for
coroots.
-/
noncomputable def Base.mk' (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    P.Base where
  support := (toFinite s).toFinset
  linearIndepOn_root := by simpa
  linearIndepOn_coroot := by have : Fintype ι := Fintype.ofFinite ι; simpa
  root_mem_or_neg_mem i := by simpa using hsp i
  coroot_mem_or_neg_mem i := by simpa using coroot_mem_or_neg_mem_closure_of_root P s hli hsp i
/-
**RootPairing.nonempty_base** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：nonempty_base : Nonempty P.Base
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.exists_dual_forall_apply_ne_zero`：Module.exists_dual_forall_apply
_ne_zero (v : ι -> M) (hv : forall i, v i != 0) : exists f : Dual K M, forall i,
 f (v i) != 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `RootPairing.linearIndepOn_root_baseOf`：linearIndepOn_root_baseOf (f : M 
->+ Rat) (hf : forall i, f (P.root i) != 0) : LinearIndepOn R P.root (baseOf P.r
oot f)
· 使用定理 `IsAddIndecomposable.mem_or_neg_mem_closure_baseOf`：∀ {ι : Type u_1} {G :
 Type u_3} {S : Type u_4} [inst : AddCommGroup G] [inst_1 : LinearOrder S] [Fini
te ι]   [inst_3 : InvolutiveNeg ι] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nonempty_base : Nonempty P.Base := by
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  obtain ⟨f, hf⟩ : ∃ f : Dual ℚ M, ∀ i, f (P.root i) ≠ 0 :=
    exists_dual_forall_apply_ne_zero P.root <| by simp [P.ne_zero]
  let := P.indexNeg
  exact ⟨Base.mk' P (baseOf P.root (f : M →+ ℚ)) (P.linearIndepOn_root_baseOf f hf)
    (fun i ↦ mem_or_neg_mem_closure_baseOf P.root (f : M →+ ℚ) i (hf i) (by simp))⟩

end Field

end RootPairing

