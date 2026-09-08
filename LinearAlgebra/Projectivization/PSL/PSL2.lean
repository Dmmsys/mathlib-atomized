/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer

/-!
-/

@[expose] public section

variable {ι F : Type*} [Field F] [DecidableEq ι] [Fintype ι]

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace SL2Gen

/-- A transvection `transvection i j hij b` lies in `lineStab (span F {Pi.single i 1})`. -/
/-
**SL2Gen.transvection_mem_lineStab** 是 Mathlib 中的一个引理，位于命名空间 `SL2Gen`。
形式化陈述：transvection_mem_lineStab {i j : ι} (hij : i != j) (b : F) : transvection 
hij b in lineStab (Submodule.span F {(Pi.single i (1 : F) : ι -> F)})
参数：hij : i != j；b : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Matrix.single_mulVec_eq`：single_mulVec_eq [Fintype n] [NonAssocSemiring 
α] (i j : n) (b : α) (w : n -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i 
(1 : α)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A transvection `transvection i j hij b` lies in `lineStab (span F {Pi.single i 1
})`.
-/
lemma transvection_mem_lineStab {i j : ι} (hij : i ≠ j) (b : F) :
    transvection hij b ∈ lineStab (Submodule.span F {(Pi.single i (1 : F) : ι → F)}) :=
  fun w ↦ Submodule.mem_span_singleton.2 ⟨b * w j, by simp [mul_smul,
    Matrix.SpecialLinearGroup.smul_def, transvection_coe, add_smul, Matrix.single_mulVec_eq]⟩

/-- Every transvection in `SL ι F` whose indices are `(i₁, i₂)` or `(i₂, i₁)` is in the join
of `lineStab(span F {e_{i₁}})` and `lineStab(span F {e_{i₂}})`. -/
/-
**SL2Gen.transvection_mem_lineStab_sup** 是 Mathlib 中的一个引理，位于命名空间 `SL2Gen`。
形式化陈述：transvection_mem_lineStab_sup (t : TransvectionStruct (Fin 2) F) : t.toSpe
cialLinearGroup in lineStab (Submodule.span F {(Pi.single 0 1 : Fin 2 -> F)}) ⊔ 
lineStab (Submodule.span F {(Pi.single 1 1 : Fin 2 -> F)})
参数：t : TransvectionStruct (Fin 2) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subgroup.mem_sup_left`：mem_sup_left {S T : Subgroup G} : forall {x : G},
 x in S -> x in S ⊔ T
· 使用引理 `SL2Gen.transvection_mem_lineStab`：transvection_mem_lineStab {i j : ι} (h
ij : i != j) (b : F) : transvection hij b in lineStab (Submodule.span F {(Pi.sin
gle i (1 : F) : ι -> F…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Subgroup.mem_sup_right`：mem_sup_right {S T : Subgroup G} : forall {x : G
}, x in T -> x in S ⊔ T
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
Every transvection in `SL ι F` whose indices are `(i₁, i₂)` or `(i₂, i₁)` is in 
the join
of `lineStab(span F {e_{i₁}})` and `lineStab(span F {e_{i₂}})`.
-/
lemma transvection_mem_lineStab_sup (t : TransvectionStruct (Fin 2) F) :
    t.toSpecialLinearGroup ∈
      lineStab (Submodule.span F {(Pi.single 0 1 : Fin 2 → F)})
      ⊔ lineStab (Submodule.span F {(Pi.single 1 1 : Fin 2 → F)}) := by
  obtain ⟨i, j, hij, c⟩ := t
  simp only [Fin.isValue, TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j <;> try tauto
  · exact Subgroup.mem_sup_left <| transvection_mem_lineStab zero_ne_one c
  · exact Subgroup.mem_sup_right <| transvection_mem_lineStab one_ne_zero c

/-- SL-level generation: in the 2-element-index case, the join of the two `lineStab` subgroups
attached to the two coordinate axes is all of `SL ι F`. -/
/-
**SL2Gen.SL_card_two_lineStab_sup_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SL2Gen`。
形式化陈述：SL_card_two_lineStab_sup_eq_top : lineStab (Submodule.span F {(Pi.single 0
 1: Fin 2 -> F)}) ⊔ lineStab (Submodule.span F {(Pi.single 1 1: Fin 2 -> F)}) = 
(⊤ : Subgroup SL(2, F))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Matrix.SL2.transvection_induction`：∀ {F : Type u_1} [inst : Field F] (P 
: Matrix.SpecialLinearGroup (Fin 2) F → Prop),   (∀ (i j : Fin 2) (h : i ≠ j) (c
 : F), P (Matrix.Specia…
· 使用引理 `SL2Gen.transvection_mem_lineStab_sup`：transvection_mem_lineStab_sup (t :
 TransvectionStruct (Fin 2) F) : t.toSpecialLinearGroup in lineStab (Submodule.s
pan F {(Pi.single 0 1 : Fi…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
SL-level generation: in the 2-element-index case, the join of the two `lineStab`
 subgroups
attached to the two coordinate axes is all of `SL ι F`.
-/
lemma SL_card_two_lineStab_sup_eq_top :
    lineStab (Submodule.span F {(Pi.single 0 1: Fin 2 → F)}) ⊔
      lineStab (Submodule.span F {(Pi.single 1 1: Fin 2 → F)}) =
      (⊤ : Subgroup SL(2, F)) :=
  le_antisymm le_top fun M _ ↦ SL2.transvection_induction _
      (fun i j hij a ↦ by simpa using transvection_mem_lineStab_sup ⟨i, j, hij, a⟩)
      (fun _ _ ↦ mul_mem) M

end SL2Gen

open scoped LinearAlgebra.Projectivization

/-- At the SL level: when `Fintype.card ι = 2`, the supremum over all projective points of
the `lineStab` subgroups equals `⊤` in `SL ι F`. -/
/-
**PSL.iSup_lineStab_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PSL.iSup_lineStab_eq_top : (⨆ p : ℙ F (Fin 2 -> F), lineStab p.submodule) 
= (⊤ : Subgroup SL(2, F))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.single_ne_zero_iff`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : 
ι) → Zero (M i)] [inst_1 : DecidableEq ι] {i : ι} {x : M i},   Pi.single i x ≠ 0
 ↔ x ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.submodule_mk`：submodule_mk (v : V) (hv : v != 0) : (mk 
K v hv).submodule = K ∙ v
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用引理 `SL2Gen.SL_card_two_lineStab_sup_eq_top`：SL_card_two_lineStab_sup_eq_top 
: lineStab (Submodule.span F {(Pi.single 0 1: Fin 2 -> F)}) ⊔ lineStab (Submodul
e.span F {(Pi.single 1 1: Fi…

--- 原说明 ---
At the SL level: when `Fintype.card ι = 2`, the supremum over all projective poi
nts of
the `lineStab` subgroups equals `⊤` in `SL ι F`.
-/
lemma PSL.iSup_lineStab_eq_top :
    (⨆ p : ℙ F (Fin 2 → F), lineStab p.submodule) = (⊤ : Subgroup SL(2, F)) := by
  refine le_antisymm le_top (SL2Gen.SL_card_two_lineStab_sup_eq_top (F := F) ▸
    sup_le ?_ ?_)
  <;> rw [← Projectivization.submodule_mk (K := F) _ (Pi.single_ne_zero_iff.2 one_ne_zero)]
  <;> exact le_iSup_iff.2 fun b a ↦ a _

/-- The Iwasawa generator property: when `Fintype.card ι = 2`, the supremum of the
`iwasawaT` subgroups equals all of `PSL`. -/
/-
**PSL.iSup_iwasawaT_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PSL.iSup_iwasawaT_eq_top : iSup (PSL.iwasawaT (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_iSup`：map_iSup {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup
 G) : (iSup s).map f = ⨆ i, (s i).map f
· 使用引理 `PSL.iSup_lineStab_eq_top`：PSL.iSup_lineStab_eq_top : (⨆ p : ℙ F (Fin 2 -
> F), lineStab p.submodule) = (⊤ : Subgroup SL(2, F))
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)

--- 原说明 ---
The Iwasawa generator property: when `Fintype.card ι = 2`, the supremum of the
`iwasawaT` subgroups equals all of `PSL`.
-/
lemma PSL.iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) = ⊤ := by
  have step1 : iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
        (⨆ p : ℙ F (Fin 2 → F),
          Matrix.SpecialLinearGroup.lineStab (F := F) (ι := Fin 2) p.submodule) := by
    rw [Subgroup.map_iSup]
  rw [step1, PSL.iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

open MulAction

/-- The Iwasawa structure on PSL(2, F). -/
/-
**PSL2.Iwasawa** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PSL2.Iwasawa : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 -> F)) where T
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `PSL.iSup_iwasawaT_eq_top`：PSL.iSup_iwasawaT_eq_top : iSup (PSL.iwasawaT 
(F

--- 原说明 ---
The Iwasawa structure on PSL(2, F).
-/
noncomputable abbrev PSL2.Iwasawa : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 2) p.submodule) := by
      rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g_SL, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change Subgroup.map _ _ = _
    rw [PSL.smul_submodule, Matrix.SpecialLinearGroup.lineStab_smul,
      PSL.iwasawaT_map_conj]
  is_generator := PSL.iSup_iwasawaT_eq_top

namespace SL2Simple

open Matrix.SpecialLinearGroup

/-- `commutator (PSL ι F) = ⊤`. -/
/-
**SL2Simple.PSL_commutator_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SL2Simple`。
形式化陈述：PSL_commutator_eq_top (hF : exists a : F, a != 0 ∧ a ^ 2 != 1) : commutato
r PSL(2, F) = ⊤
参数：hF : exists a : F, a != 0 ∧ a ^ 2 != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SL2.commutator_eq_top`：∀ {F : Type u_1} [inst : Field F] {a : F},
 a ≠ 0 → a ^ 2 ≠ 1 → commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤
· 使用定理 `Group.IsPerfect.commutator_eq_top`：∀ {G : Type u_1} {inst : Group G} [se
lf : Group.IsPerfect G], commutator G = ⊤

--- 原说明 ---
`commutator (PSL ι F) = ⊤`.
-/
lemma PSL_commutator_eq_top (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator PSL(2, F) = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top ha hasq⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  exact this.commutator_eq_top

/-- `PSL ι F` is nontrivial whenever `ι` has at least two elements (and `F` is a field,
hence in particular nontrivial). -/
/-
**SL2Simple.PSL_nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `SL2Simple`。
形式化陈述：PSL_nontrivial [Nontrivial ι] : Nontrivial (Matrix.ProjectiveSpecialLinear
Group ι F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.SpecialLinearGroup.transvection_mem_center_iff`：transvection_mem_
center_iff {i j : ι} (hij : i != j) (b : F) : transvection hij b in Subgroup.cen
ter (SpecialLinearGroup ι F) ↔ b = 0
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N

--- 原说明 ---
`PSL ι F` is nontrivial whenever `ι` has at least two elements (and `F` is a fie
ld,
hence in particular nontrivial).
-/
instance PSL_nontrivial [Nontrivial ι] :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup ι F) := by
  obtain ⟨i₁, i₂, hij⟩ := exists_pair_ne ι
  set g : Matrix.SpecialLinearGroup ι F := transvection hij 1
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F),
    1, fun h ↦ one_ne_zero (α := F) ?_⟩⟩
  rwa [QuotientGroup.eq_one_iff, transvection_mem_center_iff] at h

end SL2Simple

/-
**Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (hF : exists a : F, a
 != 0 ∧ a ^ 2 != 1) : IsSimpleGroup PSL(2, F)
参数：hF : exists a : F, a != 0 ∧ a ^ 2 != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IwasawaStructure.isSimpleGroup`：isSimpleGroup [Nontrivial M] (
is_perfect : commutator M = ⊤) [IsQuasiPreprimitive M α] (IwaS : IwasawaStructur
e M α) (is_faithful : Faithful…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SL2Simple.PSL_commutator_eq_top`：PSL_commutator_eq_top (hF : exists a : 
F, a != 0 ∧ a ^ 2 != 1) : commutator PSL(2, F) = ⊤
· 使用定理 `MulAction.IsPreprimitive.isQuasiPreprimitive`：∀ {M : Type u_3} [inst : G
roup M] {α : Type u_4} [inst_1 : MulAction M α] [MulAction.IsPreprimitive M α], 
  MulAction.IsQuasiPreprimitive M …
· 使用定理 `Projectivization.instIsPreprimitiveProjectiveSpecialLinearGroupForall`：∀
 {K : Type u_1} [inst : Field K] {ι : Type u_3} [inst_1 : Fintype ι] [inst_2 : D
ecidableEq ι],   MulAction.IsPreprimitive (Matrix.Projectiv…
· 使用定理 `Projectivization.instFaithfulSMulProjectiveSpecialLinearGroupForall`：∀ {
K : Type u_1} [inst : Field K] {ι : Type u_3} [inst_1 : Fintype ι] [inst_2 : Dec
idableEq ι],   FaithfulSMul (Matrix.ProjectiveSpecialLine…
-/
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    IsSimpleGroup PSL(2, F) :=
  MulAction.IwasawaStructure.isSimpleGroup
    (SL2Simple.PSL_commutator_eq_top hF) PSL2.Iwasawa inferInstance
/-
**field_cond_of_four_le_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma field_cond_of_four_le_card (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega
/-
**Matrix.ProjectiveSpecialLinearGroup.rank_two_simple** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (hF : 4 <= Nat.card F)
 : IsSimpleGroup PSL(2, F)
参数：hF : 4 <= Nat.card F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'`：Matrix.ProjectiveS
pecialLinearGroup.rank_two_simple' (hF : exists a : F, a != 0 ∧ a ^ 2 != 1) : Is
SimpleGroup PSL(2, F)
· 使用定理 `_private.Mathlib.LinearAlgebra.Projectivization.PSL.PSL2.0.field_cond_of
_four_le_card`：∀ {F : Type u_2} [inst : Field F], 4 ≤ Nat.card F → ∃ a, a ≠ 0 ∧ 
a ^ 2 ≠ 1
-/
theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup PSL(2, F) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_cond_of_four_le_card hF)
