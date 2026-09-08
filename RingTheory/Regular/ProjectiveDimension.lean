/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.RegularSequence

/-!

# ProjectiveDimension of quotient by regular element

For `M` a finitely generated module over Noetherian local ring `R` and an `M`-regular element `x`
contained in the unique maximal ideal of `R`, `projdim(M/xM) = projdim(M) + 1`.
The analogous version for quotient regular sequence is also provided.

## Main Results

* `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` : For `M` a finitely
  generated module over Noetherian local ring `R` and an `M`-regular element `x` contained in
  the unique maximal ideal of `R`, `projdim(M/xM) = projdim(M) + 1`

-/

@[expose] public section

universe v u

variable {R : Type u} [CommRing R] [Small.{v} R]

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

namespace ModuleCat

section

variable [IsNoetherianRing R]

/-
**ModuleCat.hasProjectiveDimensionLT_of_forall_finite** 是 Mathlib 中的一个引理，位于命名空间 
`ModuleCat`。
形式化陈述：hasProjectiveDimensionLT_of_forall_finite (M : ModuleCat.{v} R) [Module.Fi
nite R M] (n : Nat) (h : forall L : ModuleCat.{v} R, Module.Finite R L -> Subsin
gleton (Ext M L n)) : HasProjectiveDimensionLT M n
参数：M : ModuleCat.{v} R；n : Nat；h : forall L : ModuleCat.{v} R, Module.Finite R L
 -> Subsingleton (Ext M L n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
 {X : C},   CategoryTheory.Limits.IsZero X → Cat…
· 使用定理 `Module.exists_finite_presentation`：Module.exists_finite_presentation [Sm
all.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : exis
ts (P : Type v) (_ : Ad…
· 使用定理 `LinearMap.shortExact_shortComplexKer`：LinearMap.shortExact_shortComplexK
er {f : M ->ₗ[R] N} (h : Function.Surjective f) : f.shortComplexKer.ShortExact w
here exact
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`：covariant_sequence
_exact₃ {n₀ : Nat} (x₃ : Ext X S.X₃ n₀) {n₁ : Nat} (hn₁ : n₀ + 1 = n₁) (hx₃ : x₃
.comp hS.extClass hn₁ = 0) : exists (x₂ : …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_bijective`：mk₀_bijective : Function.Bijec
tive (mk₀ (X
· 使用定理 `CategoryTheory.Retract.projective`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Retract X Y)   [p : CategoryTh
eory.Projective Y], Cat…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀`：mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y
 ⟶ Z) : (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`：
hasProjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Projective S.X₂) : HasProjective
DimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n …
· 使用定理 `CategoryTheory.Abelian.Ext.subsingleton_of_projective`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [i
nst_2 : CategoryTheory.HasExt C] (P Y : C) …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CategoryTheory.ComposableArrows.Exact.isIso_map'`：∀ {C : Type u_2} [inst
 : CategoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.Preadditive C]
   [CategoryTheory.Balanced C] {n : ℕ}…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
（共 38 条，此处仅展示前 30 条）
-/
lemma hasProjectiveDimensionLT_of_forall_finite (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (h : ∀ L : ModuleCat.{v} R, Module.Finite R L → Subsingleton (Ext M L n)) :
    HasProjectiveDimensionLT M n := by
  induction n generalizing M with
  | zero =>
    have : Subsingleton (M ⟶ M) := Ext.homEquiv₀.subsingleton_congr.mp (h M ‹_›)
    have : Limits.IsZero M := (Limits.IsZero.iff_id_eq_zero M).mpr (Subsingleton.eq_zero (𝟙 M))
    exact this.hasProjectiveDimensionLT_zero
  | succ n hn =>
    rcases Module.exists_finite_presentation R M with ⟨_, _, _, _, _, f, surjf⟩
    let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    match n with
    | 0 =>
      simp only [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      have : Subsingleton (Ext M S.X₁ 1) := h S.X₁ inferInstance
      rcases Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ (𝟙 M)) (zero_add 1)
        (Subsingleton.eq_zero _) with ⟨f', hf'⟩
      rcases (Ext.mk₀_bijective M S.X₂).2 f' with ⟨f, hf⟩
      rw [← hf, Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).1.eq_iff] at hf'
      exact (Retract.mk f S.g hf').projective
    | n + 1 =>
      rw [hS.hasProjectiveDimensionLT_X₃_iff n inferInstance]
      have (L : ModuleCat.{v} R) : Subsingleton (Ext S.X₁ L (n + 1)) ↔
        Subsingleton (Ext M L (n + 2)) := by
        have (m : ℕ) : Subsingleton (Ext S.X₂ L (m + 1)) := Ext.subsingleton_of_projective S.X₂ L m
        have isi : IsIso (AddCommGrpCat.ofHom (hS.extClass.precomp L (add_comm 1 _))) :=
          (Ext.contravariantSequence_exact hS L (n + 1) (n + 2)
            (add_comm 1 _)).isIso_map' 1 (by decide)
              ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
                ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt _)
        exact (asIso (AddCommGrpCat.ofHom (hS.extClass.precomp L
          (add_comm 1 _)))).addCommGroupIsoToAddEquiv.subsingleton_congr
      apply hn S.X₁
      simpa [this] using h

end

variable [IsLocalRing R] [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular** 是 Mathlib
 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (M : ModuleCat.{v
} R) [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x in maximalId
eal R) : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDime
nsion M + 1
参数：M : ModuleCat.{v} R；x : R；reg : IsSMulRegular M x；mem : x in maximalIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.instSubsingletonQuotient`：∀ {R : Type u_1} {M : Type 
u_2} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p
 : Submodule R M} [Subsingleton M…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `nontrivial_quotSMulTop_of_mem_maximalIdeal`：nontrivial_quotSMulTop_of_me
m_maximalIdeal {x : R} (mem : x in maximalIdeal R) : Nontrivial (QuotSMulTop x L
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.projectiveDimension_le_iff`：projectiveDimension_le_iff (X
 : C) (n : Nat) : projectiveDimension X <= n ↔ HasProjectiveDimensionLE X n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `QuotSMulTop.mem_annihilator`：mem_annihilator (x : R) : x in Module.annih
ilator R (QuotSMulTop x M)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.annihilator_eq_bot`：Module.annihilator_eq_bot {R M} [Ring R] [Add
CommGroup M] [Module R M] : Module.annihilator R M = ⊥ ↔ FaithfulSMul R M
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_subsingleton`：∀ (R : Type u) (N : Type z) [inst : Semirin
g R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R N]   [Subsingleton N],
 Module.Free R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `IsSMulRegular.smulShortComplex_shortExact`：IsSMulRegular.smulShortComple
x_shortExact {r : R} (reg : IsSMulRegular M r) : (ModuleCat.smulShortComplex M r
).ShortExact where exact
· 使用引理 `ModuleCat.hasProjectiveDimensionLT_of_forall_finite`：hasProjectiveDimens
ionLT_of_forall_finite (M : ModuleCat.{v} R) [Module.Finite R M] (n : Nat) (h : 
forall L : ModuleCat.{v} R, Module.Finite…
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用引理 `CategoryTheory.HasProjectiveDimensionLT.subsingleton`：subsingleton [hX :
 HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) : Subsingleton (E
xt.{w} X Y i)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 53 条，此处仅展示前 30 条）
-/
lemma projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (M : ModuleCat.{v} R)
    [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension M + 1 := by
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
    contrapose! h
    exact (nontrivial_quotSMulTop_of_mem_maximalIdeal M mem)
  have aux (n : ℕ) : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) ≤ n ↔
    projectiveDimension M + 1 ≤ n := by
    match n with
    | 0 =>
      rw [projectiveDimension_le_iff]
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
        CharP.cast_eq_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton, sub, ← IsProjective.iff_projective]
      refine ⟨fun h ↦ ?_, fun h ↦ Projective.of_free⟩
      have : Module.Free R (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
      by_contra! ntr
      have := QuotSMulTop.mem_annihilator M x
      simp only [annihilator_eq_bot.mpr inferInstance, Submodule.mem_bot] at this
      simp only [this, IsSMulRegular.zero_iff_subsingleton] at reg
      absurd not_subsingleton_iff_nontrivial.mpr ntr
      infer_instance
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      simp only [ENat.WithBot.add_le_add_natCast_right_iff, projectiveDimension_le_iff]
      let S := M.smulShortComplex x
      have hS : S.ShortExact := reg.smulShortComplex_shortExact
      refine ⟨fun h ↦ ?_, fun h ↦ hS.hasProjectiveDimensionLT_X₃ (n + 1) h
        (hasProjectiveDimensionLT_of_ge M (n + 1) (n + 2) (Nat.le_add_right _ 1))⟩
      apply hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton (ModuleCat.of R (QuotSMulTop x M))
        (n + 2) _ (le_refl _) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : S.f = x • 𝟙 M := rfl
      simp only [S, this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext M L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) mem
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using sub.symm
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
/-
**ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular** 是 Ma
thlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular (M : ModuleC
at.{v} R) [Nontrivial M] [Module.Finite R M] (rs : List R) (reg : IsWeaklyRegula
r M rs) (mem : forall r in rs, r in maximalIdeal R) : projectiveDimension (Modul
eCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) = projectiveDimension M +
 rs.length
参数：M : ModuleCat.{v} R；rs : List R；reg : IsWeaklyRegular M rs；mem : forall r in 
rs, r in maximalIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `Ideal.ofList_nil`：∀ {R : Type u_1} [inst : Semiring R], Ideal.ofList [] 
= ⊥
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.projectiveDimension_eq_of_iso`：projectiveDimension_eq_of_
iso {X Y : C} (e : X ≅ Y) : projectiveDimension X = projectiveDimension Y
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `nontrivial_quotSMulTop_of_mem_maximalIdeal`：nontrivial_quotSMulTop_of_me
m_maximalIdeal {x : R} (mem : x in maximalIdeal R) : Nontrivial (QuotSMulTop x L
)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`：proj
ectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (M : ModuleCat.{v} R) [Modu
le.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular (M : ModuleCat.{v} R)
    [Nontrivial M] [Module.Finite R M] (rs : List R) (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) =
    projectiveDimension M + rs.length := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero =>
    rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using projectiveDimension_eq_of_iso (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  | succ n hn =>
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [isWeaklyRegular_cons_iff] at reg
      have := nontrivial_quotSMulTop_of_mem_maximalIdeal M mem.1
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      rw [Nat.cast_add, Nat.cast_one, projectiveDimension_eq_of_iso
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso, add_comm _ 1,
        ← add_assoc, ← projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x reg.1 mem.1,
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' reg.2 mem.2 len]
/-
**ModuleCat.projectiveDimension_quotient_eq_length** 是 Mathlib 中的一个引理，位于命名空间 `Mo
duleCat`。
形式化陈述：projectiveDimension_quotient_eq_length (rs : List R) (reg : IsRegular R rs
) : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) = rs
.length
参数：rs : List R；reg : IsRegular R rs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `RingTheory.Sequence.IsRegular.top_ne_smul`：∀ {R : Type u_1} {M : Type u_
3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
{rs : List R}, RingTheory.Seque…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_span`：mem_span {s : Set α} (x) : x in span s ↔ forall p : Idea
l α, s subseteq p -> x in p
· 使用定理 `Submodule.Quotient.instSmallQuotient`：∀ {R : Type u_3} {M : Type u_4} [i
nst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} [Small.{u, u_4}…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.projectiveDimension_eq_of_iso`：projectiveDimension_eq_of_
iso {X Y : C} (e : X ≅ Y) : projectiveDimension X = projectiveDimension Y
· 使用引理 `ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular`
：projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular (M : ModuleCat.{v
} R) [Nontrivial M] [Module.Finite R M] (rs : List R) (reg : …
· 使用定理 `instNontrivialShrink`：∀ {α : Type u} [inst : Small.{v, u} α] [Nontrivial
 α], Nontrivial (Shrink.{v, u} α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `LinearEquiv.isWeaklyRegular_congr`：∀ {R : Type u_1} {M : Type u_3} {M₂ :
 Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup 
M₂]   [inst_3 : _root_.…
· 使用定理 `RingTheory.Sequence.IsRegular.toIsWeaklyRegular`：∀ {R : Type u_1} {M : T
ype u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R
 M]   {rs : List R}, RingTheory.Seque…
· 使用引理 `ModuleCat.projectiveDimension_eq_zero_of_projective`：projectiveDimension
_eq_zero_of_projective (M : ModuleCat.{v} R) [Nontrivial M] [Projective M] : pro
jectiveDimension M = 0
· 使用定理 `Module.instProjectiveShrink`：∀ {R : Type u_1} [inst : Semiring R] {M : T
ype u_3} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : Sma
ll.{w, u_3} M] [M…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma projectiveDimension_quotient_eq_length (rs : List R) (reg : IsRegular R rs) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) = rs.length := by
  have mem_max : ∀ x ∈ rs, x ∈ maximalIdeal R := by
    intro x hx
    apply IsLocalRing.le_maximalIdeal reg.2.symm
    simpa using (Ideal.mem_span x).mpr fun p a ↦ a hx
  let e : (Shrink.{v} (R ⧸ Ideal.ofList rs)) ≃ₗ[R]
    (Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)) :=
    ((Shrink.linearEquiv R _).trans (Submodule.Quotient.equiv _ _ (Shrink.linearEquiv R R).symm (by
      nth_rw 1 [← (Ideal.ofList rs).mul_top, ← smul_eq_mul, Submodule.map_smul'']
      simp )))
  rw [projectiveDimension_eq_of_iso e.toModuleIso,
    projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular (ModuleCat.of R (Shrink.{v} R)) rs
    (((Shrink.linearEquiv R R).isWeaklyRegular_congr rs).mpr reg.1) mem_max,
    ModuleCat.projectiveDimension_eq_zero_of_projective, zero_add]

end ModuleCat

