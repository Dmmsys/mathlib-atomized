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
  {S : Type*} [LinearOrder S] [AddCommGroup S] [IsOrderedAddMonoid S] (f : M ->+ S)

/--
lemma `baseOf_pairwise_pairing_le_zero` / 引理 `baseOf_pairwise_pairing_le_zero`

English:
lemma baseOf_pairwise_pairing_le_zero
  statement: [CharZero R] [IsDomain R] [P.IsCrystallographic]
  proof: by
  let _i := P.indexNeg
  intro i hi j hj hne
  have := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root (by simp) f hf hi hj hne
  contrapose! this
  exact P.root_sub_root_mem_of_pairingIn_pos this hne

中文:
引理 baseOf_pairwise_pairing_le_zero
  结论: [特征零 R] [是整环 R] [P.IsCrystallographic]
  证明: by
  let _i := P.indexNeg
  intro i hi j hj hne
  have := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root (by simp) f hf hi hj hne
  contrapose! this
  exact P.root_sub_root_mem_of_pairingIn_pos this hne

Depends on / 依赖: IsAddIndecomposable, IsAddIndecomposable.pairwise_baseOf_sub_notMem, P.indexNeg, P.root, P.root_sub_root_mem_of_pairingIn_pos, contrapose, indexNeg, pairwise_baseOf_sub_notMem, root_sub_root_mem_of_pairingIn_pos
-/
lemma baseOf_pairwise_pairing_le_zero [CharZero R] [IsDomain R] [P.IsCrystallographic]
    (hf : forall i, f (P.root i) != 0) :
    (baseOf P.root f).Pairwise fun i j => P.pairingIn Int i j <= 0 := by
  let _i := P.indexNeg
  intro i hi j hj hne
  have := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root (by simp) f hf hi hj hne
  contrapose! this
  exact P.root_sub_root_mem_of_pairingIn_pos this hne

/--
lemma `linearIndepOn_root_baseOf'` / 引理 `linearIndepOn_root_baseOf'`

English:
lemma linearIndepOn_root_baseOf'
  statement: [IsDomain R] {S : Type*}
  proof: by
  have : CharZero R := Algebra.charZero_of_charZero S R
  have : Fintype ι := Fintype.ofFinite ι
  let M₀ := span S (range P.root)
  let v (i : baseOf P.root (f : M ->+ S)) : M₀ := P.rootSpanMem S i
  change LinearIndependent S (M₀.subtype ∘ v)
  suffices LinearIndependent S v by
    rwa [LinearM

中文:
引理 linearIndepOn_root_baseOf'
  结论: [是整环 R] {S : 类型}
  证明: by
  have : CharZero R := Algebra.charZero_of_charZero S R
  have : Fintype ι := Fintype.ofFinite ι
  let M₀ := span S (range P.root)
  let v (i : baseOf P.root (f : M ->+ S)) : M₀ := P.rootSpanMem S i
  change LinearIndependent S (M₀.subtype ∘ v)
  suffices LinearIndependent S v by
    rwa [LinearM

Depends on / 依赖: Algebra, Algebra.charZero_of_charZero, B.posForm.toQuadraticMap.PosDef, CharZero, Fintype, Fintype.ofFinite, LinearIndependent, LinearMap, LinearMap.linearIndependent_iff_of_disjoint, P.RootPositiveForm, P.posRootForm, P.root, P.rootSpanMem, PosDef, RootPositiveForm, baseOf, charZero_of_charZero, linearIndependent_iff_of_disjoint, ofFinite, posForm
-/
lemma linearIndepOn_root_baseOf' [IsDomain R] {S : Type*}
    [LinearOrder S] [CommRing S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]
    [P.IsValuedIn S] [P.IsCrystallographic]
    (f : Dual S M) (hf : forall i, f (P.root i) != 0) :
    LinearIndepOn S P.root (baseOf P.root (f : M ->+ S)) := by
  have : CharZero R := Algebra.charZero_of_charZero S R
  have : Fintype ι := Fintype.ofFinite ι
  let M₀ := span S (range P.root)
  let v (i : baseOf P.root (f : M ->+ S)) : M₀ := P.rootSpanMem S i
  change LinearIndependent S (M₀.subtype ∘ v)
  suffices LinearIndependent S v by
    rwa [LinearMap.linearIndependent_iff_of_disjoint M₀.subtype (by simp)]
  let f' : Dual S M₀ := f ∘ₗ M₀.subtype
  obtain ⟨B, hB⟩ : exists B : P.RootPositiveForm S, B.posForm.toQuadraticMap.PosDef :=
    ⟨P.posRootForm S, by simpa using P.posRootForm_rootFormIn_posDef S⟩
  have hp (i : baseOf P.root (f : M ->+ S)) : 0 < f' (v i) := by obtain ⟨i, -, hi⟩ := i; simpa
  have hn : Pairwise fun (i j : baseOf P.root (f : M ->+ S)) => B.posForm (v i) (v j) <= 0 := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    rw [B.posForm_apply_root_root_le_zero_iff]; rw [← P.algebraMap_pairingIn' S Int]
    simpa using P.baseOf_pairwise_pairing_le_zero _ hf (by simpa) (by simpa) (by aesop : i != j)
  exact LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero B.posForm hB f' v hp hn

/--
lemma `ncard_eq_finrank_of_linearIndepOn_of` / 引理 `ncard_eq_finrank_of_linearIndepOn_of`

English:
lemma ncard_eq_finrank_of_linearIndepOn_of
  statement: [P.IsRootSystem] [Nontrivial R]
  proof: by
let b : Basis s R M := Basis.mk hli by
    rw [← IsRootSystem.span_root_eq_top (P := P)]; rw [span_le]; rw [← span_span_of_tower (R := Int)]
    rintro - ⟨i, rfl⟩
    apply subset_span
    rcases hsp i with hi | hi <;>
      simpa [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, span_int_eq_addSu

中文:
引理 ncard_eq_finrank_of_linearIndepOn_of
  结论: [P.是RootSystem] [非平凡 R]
  证明: by
let b : Basis s R M := Basis.mk hli by
    rw [← IsRootSystem.span_root_eq_top (P := P)]; rw [span_le]; rw [← span_span_of_tower (R := Int)]
    rintro - ⟨i, rfl⟩
    apply subset_span
    rcases hsp i with hi | hi <;>
      simpa [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, span_int_eq_addSu

Depends on / 依赖: AddSubgroup, AddSubgroup.le_closure_toAddSubmonoid, Basis.mk, Fintype, Fintype.ofFinite, IsRootSystem, IsRootSystem.span_root_eq_top, P.root, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_toAddSubgroup, finrank_eq_card_basis, image_eq_range, le_closure_toAddSubmonoid, mem_coe, mem_toAddSubgroup, ncard_eq_toFinset_card, ofFinite, span_int_eq_addSubgroupClosure
-/
lemma ncard_eq_finrank_of_linearIndepOn_of [P.IsRootSystem] [Nontrivial R]
    {s : Set ι}
    (hli : LinearIndepOn R P.root s)
    (hsp : forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨
               -P.root i in AddSubmonoid.closure (P.root '' s)) :
    s.ncard = finrank R M := by
let b : Basis s R M := Basis.mk hli by
    rw [← IsRootSystem.span_root_eq_top (P := P)]; rw [span_le]; rw [← span_span_of_tower (R := Int)]
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
/--
lemma `linearIndepOn_root_baseOf` / 引理 `linearIndepOn_root_baseOf`

English:
lemma linearIndepOn_root_baseOf
  given: (f : M ->+ Rat) (hf : forall i, f (P.root i) != 0)
  proof: by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  let := P.indexNeg
  have : Fintype (baseOf P.root f) := Fintype.ofFinite _
  let v (i : baseOf P.root f) : P.rootSpan Rat := P.rootSpanMem Rat i
  change LinearIndepende

中文:
引理 linearIndepOn_root_baseOf
  条件: (f : M ->+ 有理数) (hf : 对任意 i, f (P.root i) != 0)
  证明: by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  let := P.indexNeg
  have : Fintype (baseOf P.root f) := Fintype.ofFinite _
  let v (i : baseOf P.root f) : P.rootSpan Rat := P.rootSpanMem Rat i
  change LinearIndepende

Depends on / 依赖: Fintype, Fintype.ofFinite, LinearIndependent, Module, Module.compHom, P.indexNeg, P.root, P.rootSpan, P.rootSpanMem, algebraMap, baseOf, compHom, eq_top_iff, h_span, indexNeg, map_, ofFinite, rootSpan, rootSpanMem, subtype
-/
lemma linearIndepOn_root_baseOf (f : M ->+ Rat) (hf : forall i, f (P.root i) != 0) :
    LinearIndepOn R P.root (baseOf P.root f) := by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  let := P.indexNeg
  have : Fintype (baseOf P.root f) := Fintype.ofFinite _
  let v (i : baseOf P.root f) : P.rootSpan Rat := P.rootSpanMem Rat i
  change LinearIndependent R ((P.rootSpan Rat).subtype ∘ v)
  have h_span : span Rat (range v) = ⊤ := by
    suffices span Rat (range v) = span Rat (range (P.rootSpanMem Rat)) by
      rw [this]; rw [eq_top_iff]; rw [← (P.rootSpan Rat).subtype.map_le_map_iff' (by simp)]; rw [map_span]; rw [← image_univ]; rw [← image_comp]
      simp
    apply le_antisymm (span_mono fun x i => by aesop) (span_le.mpr ?_)
    rintro - ⟨i, rfl⟩
    suffices (P.rootSpanMem Rat i : M) in span Rat (P.root '' baseOf P.root f) by
      rw [← (injective_subtype (P.rootSpan Rat)).mem_set_image]; rw [← map_coe]; rw [SetLike.mem_coe]; rw [map_span]; rw [← image_univ]; rw [← image_comp]
      convert! this
      aesop
    rw [← span_span_of_tower Int]; rw [← Submodule.coe_toAddSubgroup]; rw [span_int_eq_addSubgroupClosure]; rw [AddSubgroup.closure_image_isAddIndecomposable_baseOf P.root (by simp) f (by simpa)]
exact subset_span AddSubgroup.subset_closure by simp
  have h_card : Nat.card (baseOf P.root f) = finrank R M := by
    let b : Basis (baseOf P.root f) Rat (P.rootSpan Rat) := by
      replace this : LinearIndependent Rat v :=
.of_comp (P.rootSpan Rat).subtype P.linearIndepOn_root_baseOf' f.toRatLinearMap hf
      exact Basis.mk this (by rw [h_span])
    rw [← RootPairing.finrank_rootSpanIn Rat P]; rw [finrank_eq_nat_card_basis b]
  replace h_span : span R (range <| (P.rootSpan Rat).subtype ∘ v) = ⊤ := by
    rw [range_comp]; rw [← span_span_of_tower Rat]; rw [span_image]; rw [h_span]
    simp
  rw [linearIndependent_iff_card_eq_finrank_span]; rw [Set.finrank]; rw [h_span]; rw [finrank_top]; rw [← h_card]; rw [Fintype.card_eq_nat_card]

/--
lemma `eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure` / 引理 `eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure`

English:
lemma eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure
  proof: by
  let _i := P.indexNeg
  have h_card : (baseOf P.root f).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) != 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root f s (by aesop) i (P.ne_zero i) (by simp) (hsp i)
    have aux (i : ι) := mem_or_neg_mem_closure_baseOf P.roo

中文:
引理 eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure
  证明: by
  let _i := P.indexNeg
  have h_card : (baseOf P.root f).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) != 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root f s (by aesop) i (P.ne_zero i) (by simp) (hsp i)
    have aux (i : ι) := mem_or_neg_mem_closure_baseOf P.roo

Depends on / 依赖: AddSubmonoid, AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure, P.indexNeg, P.linearIndepOn_root_baseOf, P.ncard_eq_finrank_of_linearIndepOn_of, P.ne_zero, P.root, apply_ne_zero_of_mem_or_neg_mem_closure, baseOf, eq_of_subset_of_, h_card, indexNeg, linearIndepOn_root_baseOf, mem_or_neg_mem_closure_baseOf, ncard_eq_finrank_of_linearIndepOn_of, ne_zero, s.ncard, subseteq
-/
lemma eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure
    (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨
               -P.root i in AddSubmonoid.closure (P.root '' s))
    (f : M ->+ Rat) (hf : forall i in s, f (P.root i) = 1) :
    s = baseOf P.root f := by
  let _i := P.indexNeg
  have h_card : (baseOf P.root f).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) != 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root f s (by aesop) i (P.ne_zero i) (by simp) (hsp i)
    have aux (i : ι) := mem_or_neg_mem_closure_baseOf P.root f i (hf' i) (by simp)
    rw [P.ncard_eq_finrank_of_linearIndepOn_of hli hsp]; rw [P.ncard_eq_finrank_of_linearIndepOn_of
      (P.linearIndepOn_root_baseOf f hf') aux]
  suffices s subseteq baseOf P.root f from eq_of_subset_of_ncard_le this (by rw [h_card])
  replace hsp (i : ι) : exists z : Int, f (P.root i) = z := by
    rcases hsp i with hi | hi
    · exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ => ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, by simp [hn, hm]⟩) hi
    · suffices exists z : Int, f (P.root (-i)) = z by obtain ⟨z, hz⟩ := this; exact ⟨-z, by simp [← hz]⟩
      replace hi : P.root (-i) in AddSubmonoid.closure (P.root '' s) := by simpa
      exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ => ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, by simp [hn, hm]⟩) hi
  refine fun i hi => ⟨by aesop, fun j hj k hk contra => ?_⟩
  obtain ⟨n, hn⟩ := hsp j
  obtain ⟨m, hm⟩ := hsp k
  replace hj : 0 < n := by simpa [hn] using hj
  replace hk : 0 < m := by simpa [hm] using hk
  replace contra : 1 = n + m := by
    replace contra := congr(f $contra)
    rwa [hf i hi, map_add, hn, hm, ← Int.cast_add, ← Int.cast_one, Int.cast_inj] at contra
  lia

/--
lemma `eq_baseOf_iff` / 引理 `eq_baseOf_iff`

English:
lemma eq_baseOf_iff
  statement: (s : Set ι) (f : M ->+ Rat)
  proof: by
  let := P.indexNeg
  refine ⟨?_, fun ⟨hli, sp⟩ => P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli sp f hf⟩
  rintro rfl
  exact ⟨P.linearIndepOn_root_baseOf f hf', fun i =>
    mem_or_neg_mem_closure_baseOf P.root f i (by simp_all) (by simp)⟩

中文:
引理 eq_baseOf_iff
  结论: (s : 集合 ι) (f : M ->+ 有理数)
  证明: by
  let := P.indexNeg
  refine ⟨?_, fun ⟨hli, sp⟩ => P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli sp f hf⟩
  rintro rfl
  exact ⟨P.linearIndepOn_root_baseOf f hf', fun i =>
    mem_or_neg_mem_closure_baseOf P.root f i (by simp_all) (by simp)⟩

Depends on / 依赖: P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure, P.indexNeg, P.linearIndepOn_root_baseOf, P.root, eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure, indexNeg, linearIndepOn_root_baseOf, mem_or_neg_mem_closure_baseOf
-/
lemma eq_baseOf_iff (s : Set ι) (f : M ->+ Rat)
    (hf : forall i in s, f (P.root i) = 1) (hf' : forall i, f (P.root i) != 0) :
    s = baseOf P.root f ↔
      LinearIndepOn R P.root s ∧
        forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨
            -P.root i in AddSubmonoid.closure (P.root '' s) := by
  let := P.indexNeg
  refine ⟨?_, fun ⟨hli, sp⟩ => P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli sp f hf⟩
  rintro rfl
  exact ⟨P.linearIndepOn_root_baseOf f hf', fun i =>
    mem_or_neg_mem_closure_baseOf P.root f i (by simp_all) (by simp)⟩

variable [P.IsReduced]

/--
lemma `baseOf_root_eq_baseOf_coroot_aux` / 引理 `baseOf_root_eq_baseOf_coroot_aux`

English:
lemma baseOf_root_eq_baseOf_coroot_aux
  proof: by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let s := baseOf P.root f
  refine fun i hi => ⟨by obtain ⟨hi, -⟩ := hi; aesop, fun j hj k hk contra => ?_⟩
  suffices i = j by grind
  obtain ⟨u, hu, v, hv, huv⟩ : existsᵉ (u >

中文:
引理 baseOf_root_eq_baseOf_coroot_aux
  证明: by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let s := baseOf P.root f
  refine fun i hi => ⟨by obtain ⟨hi, -⟩ := hi; aesop, fun j hj k hk contra => ?_⟩
  suffices i = j by grind
  obtain ⟨u, hu, v, hv, huv⟩ : existsᵉ (u >
-/
private lemma baseOf_root_eq_baseOf_coroot_aux
    (f : M ->+ Rat) (g : N ->+ Rat) (hf : forall i, f (P.root i) != 0)
    (hfg : forall i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f subseteq baseOf P.coroot (g : N ->+ Rat) := by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let s := baseOf P.root f
  refine fun i hi => ⟨by obtain ⟨hi, -⟩ := hi; aesop, fun j hj k hk contra => ?_⟩
  suffices i = j by grind
  obtain ⟨u, hu, v, hv, huv⟩ : existsᵉ (u > (0 : Rat)) (v > (0 : Rat)),
      P.root i = u • P.root j + v • P.root k := by
    let l (i : ι) := P.RootFormIn Rat (P.rootSpanMem Rat i) (P.rootSpanMem Rat i)
    have hl (i : ι) : 0 < l i := by
      simpa only [l, ← posRootForm_eq] using RootPositiveForm.zero_lt_posForm_apply_root _ _
    refine ⟨l i / l j, by simp [hl], l i / l k, by simp [hl], ?_⟩
    simp only [P.coroot_eq_polarizationEquiv_apply_root, ← map_smul, ← map_add,
      P.PolarizationEquiv.injective.eq_iff] at contra
    let l' (i : ι) := P.RootForm (P.root i) (P.root i)
    have hll' (i : ι) : l i = l' i := P.algebraMap_rootFormIn Rat _ _
    change (2 / l' i) • P.root i = (2 / l' j) • P.root j + (2 / l' k) • P.root k at contra
    replace contra := congr_arg ((2 / l' i)⁻¹ • ·) contra
    have aux₁ : 2 / l' i != 0 := by simpa using IsAnisotropic.rootForm_root_ne_zero i
    have aux₂ (j : ι) : (2 / l' i)⁻¹ * (2 / l' j) = l i / l j := by ring_nf; simp [hll']
    simp only [smul_add, smul_smul, inv_mul_cancel₀ aux₁, aux₂, one_smul] at contra
    rw [contra]
    module
  have hjk {l : ι} (hl : 0 < g (P.coroot l)) :
      exists c : P.root '' s -> Nat, ∑ x, c x • (x : M) = P.root l := by
    rwa [← Submodule.mem_span_iff_of_fintype, ← mem_toAddSubmonoid, span_nat_eq_addSubmonoidClosure,
      AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
      AddSubmonoid.mem_closure_image_pos_iff P.root f _ (P.ne_zero _), hfg]
  obtain ⟨a, ha⟩ : exists c : P.root '' s -> Nat, ∑ x, c x • (x : M) = P.root j := hjk hj
  obtain ⟨b, hb⟩ : exists d : P.root '' s -> Nat, ∑ x, d x • (x : M) = P.root k := hjk hk
  let ri : P.root '' s := ⟨P.root i, mem_image_of_mem _ hi⟩
  replace huv : u • (Nat.cast ∘ a) + v • (Nat.cast (R := Rat) ∘ b) = Pi.single ri 1 := by
    simp_rw [← ha, ← hb, Finset.smul_sum, ← Finset.sum_add_distrib, ← Nat.cast_smul_eq_nsmul Rat,
      smul_smul, ← add_smul] at huv
    have aux : P.root i = ∑ x, Pi.single (M := fun x : P.root '' s => Rat) ri 1 x • (x : M) := by
      simp [ri]
    rw [eq_comm]; rw [aux] at huv
    have hli : LinearIndepOn Rat id (P.root '' s) := by
      rw [← linearIndepOn_iff_image P.root.injective.injOn]
      exact (linearIndepOn_root_baseOf P f hf).restrict_scalars' Rat
    rw [← linearIndependent_subtype_iff] at hli
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hli huv
  obtain ⟨q, hq, hq'⟩ : exists q > (0 : Rat), P.root j = q • P.root i := by
    suffices P.root j = (a ri : Rat) • P.root i by
      refine ⟨a ri, ?_, this⟩
      by_contra contra
      replace contra : a ri = 0 := by simpa using contra
      simp [contra, P.ne_zero j] at this
    have (x : P.root '' s) (hx : x != ri) : a x = 0 := by
      replace huv : u * ↑(a x) + v * ↑(b x) = 0 := by simpa [hx] using congr($huv x)
      suffices u * (a x) = 0 by simpa [hu.ne'] using this
      have : 0 <= u * (a x) := by positivity
      have : 0 <= v * (b x) := by positivity
      grind
    replace this (x : P.root '' s) (hx : a x • (x : M) != 0) : x in ({ri} : Finset _) := by
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

/--
lemma `baseOf_root_eq_baseOf_coroot` / 引理 `baseOf_root_eq_baseOf_coroot`

English:
lemma baseOf_root_eq_baseOf_coroot
  proof: subset_antisymm (P.baseOf_root_eq_baseOf_coroot_aux f g hf hfg)
    (P.flip.baseOf_root_eq_baseOf_coroot_aux g f hg (by aesop))

中文:
引理 baseOf_root_eq_baseOf_coroot
  证明: subset_antisymm (P.baseOf_root_eq_baseOf_coroot_aux f g hf hfg)
    (P.flip.baseOf_root_eq_baseOf_coroot_aux g f hg (by aesop))

Depends on / 依赖: P.baseOf_root_eq_baseOf_coroot_aux, P.flip.baseOf_root_eq_baseOf_coroot_aux, baseOf_root_eq_baseOf_coroot_aux, subset_antisymm
-/
lemma baseOf_root_eq_baseOf_coroot
    (f : M ->+ Rat) (hf : forall i, f (P.root i) != 0)
    (g : N ->+ Rat) (hg : forall i, g (P.coroot i) != 0)
    (hfg : forall i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f = baseOf P.coroot (g : N ->+ Rat) :=
  subset_antisymm (P.baseOf_root_eq_baseOf_coroot_aux f g hf hfg)
    (P.flip.baseOf_root_eq_baseOf_coroot_aux g f hg (by aesop))

/--
lemma `coroot_mem_or_neg_mem_closure_of_root` / 引理 `coroot_mem_or_neg_mem_closure_of_root`

English:
lemma coroot_mem_or_neg_mem_closure_of_root
  statement: (s : Set ι)
  proof: by
  let _i := P.indexNeg
  let _i : Fintype ι := Fintype.ofFinite ι
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  obtain ⟨f, hf'⟩ := exists_dual_forall_apply_eq_one (hli.restrict_scalars' Rat)
  have hf := P.eq_baseOf

中文:
引理 coroot_mem_or_neg_mem_closure_of_root
  结论: (s : 集合 ι)
  证明: by
  let _i := P.indexNeg
  let _i : Fintype ι := Fintype.ofFinite ι
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  obtain ⟨f, hf'⟩ := exists_dual_forall_apply_eq_one (hli.restrict_scalars' Rat)
  have hf := P.eq_baseOf

Depends on / 依赖: AddSubmonoid, AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure, Fintype, Fintype.ofFinite, Module, Module.compHom, P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure, P.indexNeg, P.ne_zero, P.root, algebraMap, apply_ne_zero_of_mem_or_neg_mem_closure, compHom, eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure, exists_dual_forall_apply_eq_one, hli.restrict_scalars, indexNeg, ne_zero, ofFinite, restrict_scalars
-/
lemma coroot_mem_or_neg_mem_closure_of_root (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨
               -P.root i in AddSubmonoid.closure (P.root '' s))
    (i : ι) :
     P.coroot i in AddSubmonoid.closure (P.coroot '' s) ∨
    -P.coroot i in AddSubmonoid.closure (P.coroot '' s) := by
  let _i := P.indexNeg
  let _i : Fintype ι := Fintype.ofFinite ι
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat R)
  obtain ⟨f, hf'⟩ := exists_dual_forall_apply_eq_one (hli.restrict_scalars' Rat)
  have hf := P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli hsp f hf'
  have hf₀ (i : ι) : f (P.root i) != 0 :=
    AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure P.root (f : M ->+ Rat) s (by simp_all) i
      (P.ne_zero i) (by simp) (hsp i)
  have aux (i : ι) : exists q : Rat, 0 < q ∧ q = 2 / P.RootForm (P.root i) (P.root i) := by
    refine ⟨2 / P.RootFormIn Rat (P.rootSpanMem Rat i) (P.rootSpanMem Rat i), ?_, ?_⟩
    · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, ← posRootForm_eq]
      exact (P.posRootForm Rat).zero_lt_posForm_apply_root i (P.rootSpanMem Rat i).property
    · simp [← P.algebraMap_rootFormIn Rat (P.rootSpanMem Rat i) (P.rootSpanMem Rat i)]
  let g : Dual Rat N := f ∘ₗ (P.PolarizationEquiv.symm.restrictScalars Rat).toLinearMap
  have hg₀ (i : ι) : g (P.coroot i) != 0 := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀.ne', hf₀ i]
  have hg (i : ι) : 0 < g (P.coroot i) ↔ 0 < f (P.root i) := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀]
  rw [hf]; rw [P.baseOf_root_eq_baseOf_coroot f hf₀ g hg₀ (fun i => (hg i).symm)]
  exact mem_or_neg_mem_closure_baseOf P.coroot (g : N ->+ Rat) i (hg₀ i) (by simp)

/--
Definition of `Base.mk'` / `Base.mk'` 的定义

English:
definition Base.mk'
  signature: (s : Set ι)
  body: (toFinite s).toFinset
  linearIndepOn_root := by simpa
  linearIndepOn_coroot := by have : Fintype ι := Fintype.ofFinite ι; simpa
  root_mem_or_neg_mem i := by simpa using hsp i
  coroot_mem_or_neg_mem i := by simpa using coroot_mem_or_neg_mem_closure_of_root P s hli hsp i

中文:
定义 Base.mk'
  签名: (s : 集合 ι)
  定义体: (toFinite s).toFinset
  linearIndepOn_root := by simpa
  linearIndepOn_coroot := by have : Fintype ι := Fintype.ofFinite ι; simpa
  root_mem_or_neg_mem i := by simpa using hsp i
  coroot_mem_or_neg_mem i := by simpa using coroot_mem_or_neg_mem_closure_of_root P s hli hsp i

Depends on / 依赖: toFinite, toFinset
-/
noncomputable def Base.mk' (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : forall i, P.root i in AddSubmonoid.closure (P.root '' s) ∨
               -P.root i in AddSubmonoid.closure (P.root '' s)) :
    P.Base where
  support := (toFinite s).toFinset
  linearIndepOn_root := by simpa
  linearIndepOn_coroot := by have : Fintype ι := Fintype.ofFinite ι; simpa
  root_mem_or_neg_mem i := by simpa using hsp i
  coroot_mem_or_neg_mem i := by simpa using coroot_mem_or_neg_mem_closure_of_root P s hli hsp i

/--
lemma `nonempty_base` / 引理 `nonempty_base`

English:
lemma nonempty_base
  statement: Nonempty P.Base
  proof: by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  obtain ⟨f, hf⟩ : exists f : Dual Rat M, forall i, f (P.root i) != 0 :=
exists_dual_forall_apply_ne_zero P.root by simp [P.ne_zero]
  let := P.indexNeg
  exact ⟨Base.mk' P (baseOf P.root (f : M ->+ Rat)) (P.linearIndepOn_root_baseOf 

中文:
引理 nonempty_base
  结论: 非空 P.Base
  证明: by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  obtain ⟨f, hf⟩ : exists f : Dual Rat M, forall i, f (P.root i) != 0 :=
exists_dual_forall_apply_ne_zero P.root by simp [P.ne_zero]
  let := P.indexNeg
  exact ⟨Base.mk' P (baseOf P.root (f : M ->+ Rat)) (P.linearIndepOn_root_baseOf 

Depends on / 依赖: Base.mk, Module, Module.compHom, P.indexNeg, P.linearIndepOn_root_baseOf, P.ne_zero, P.root, algebraMap, baseOf, compHom, exists_dual_forall_apply_ne_zero, indexNeg, linearIndepOn_root_baseOf, mem_or_neg_mem_closure_baseOf, ne_zero
-/
lemma nonempty_base : Nonempty P.Base := by
  let _i : Module Rat M := Module.compHom M (algebraMap Rat R)
  obtain ⟨f, hf⟩ : exists f : Dual Rat M, forall i, f (P.root i) != 0 :=
exists_dual_forall_apply_ne_zero P.root by simp [P.ne_zero]
  let := P.indexNeg
  exact ⟨Base.mk' P (baseOf P.root (f : M ->+ Rat)) (P.linearIndepOn_root_baseOf f hf)
    (fun i => mem_or_neg_mem_closure_baseOf P.root (f : M ->+ Rat) i (hf i) (by simp))⟩

end Field

end RootPairing
