/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `ModuleCat.exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, Noetherian ring `R`,
  `I : Ideal R`, and finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
  the following are equivalent:
  · for any `N : ModuleCat R` finitely generated such that `Supp N ⊆ V(I)`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (R ⧸ I) M i = 0`
  · there exists a `N : ModuleCat R` finitely generated and nontrivial with `Supp N = V(I)`
    such that `∀ i < n, Ext N M i = 0`
  · there exists a `M`-regular sequence of length `n` with every element in `I`

## References

* [Commutative Algebra, Theorem 28][matsumuraCommAlg]

-/

public section

universe v u

open LinearMap RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise IsSMulRegular

variable {R : Type u} [CommRing R]

/-
**smul_top_quotSMulTop_ne_top_of_smul_top_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma smul_top_quotSMulTop_ne_top_of_smul_top_ne_top {M : Type*} [AddCommGroup M]
    [Module R M] {I : Ideal R} {r : R} (hr : r ∈ I)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop r M)) ≠ ⊤ := by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI

namespace ModuleCat

/-- The implication `(3) → (4)` of `exists_isRegular_tfae`: for `M N` finitely generated
module over Noetherian ring `R` and ideal `I` satisfying `IM < M` and `Supp N = V(I)`,
if `Ext N M i = 0` for all `i < n`,
then there exists an `M`-regular sequence of length `n` contained in `I`. -/
/-
**ModuleCat.exists_isRegular_of_exists_subsingleton_ext** 是 Mathlib 中的一个引理，位于命名空
间 `ModuleCat`。
形式化陈述：exists_isRegular_of_exists_subsingleton_ext [Small.{v} R] [IsNoetherianRin
g R] (I : Ideal R) (n : Nat) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt 
: I • (⊤ : Submodule R M) < ⊤) (N : ModuleCat.{v} R) [Module.Finite R N] (h_supp
 : Module.support R N = PrimeSpectrum.zeroLocus I) (h_ext : forall i < n, Subsin
gleton (Ext N M i)) : exists rs : List R, rs.length = n ∧ (forall r in rs, r in 
I) ∧ IsRegular M rs
参数：I : Ideal R；n : Nat；M : ModuleCat.{v} R；smul_lt : I • (⊤ : Submodule R M) < ⊤
；N : ModuleCat.{v} R；h_supp : Module.support R N = PrimeSpectrum.zeroLocus I；h_e
xt : forall i < n, Subsingleton (Ext N M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.nontrivial_iff`：nontrivial_iff : Nontrivial (Submodule R M) ↔ 
Nontrivial M
· 使用定理 `nontrivial_of_lt`：nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : 
Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `RingTheory.Sequence.isRegular_iff`：∀ {R : Type u_1} (M : Type u_3) [inst
 : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (rs : Li
st R), RingTheory.Seque…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.ofList_nil`：∀ {R : Type u_1} [inst : Semiring R], Ideal.ofList [] 
= ⊥
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用引理 `IsSMulRegular.subsingleton_linearMap_iff`：subsingleton_linearMap_iff [Is
NoetherianRing R] [Module.Finite R M] [Module.Finite R N] : Subsingleton (N ->ₗ[
R] M) ↔ exists r in Module.ann…
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `PrimeSpectrum.zeroLocus_eq_iff`：zeroLocus_eq_iff {I J : Ideal R} : zeroL
ocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGrpCat.isZero_of_iff_subsingleton`：∀ {G : Type u_1} [inst : AddCo
mmGroup G], CategoryTheory.Limits.IsZero (AddCommGrpCat.of G) ↔ Subsingleton G
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The implication `(3) → (4)` of `exists_isRegular_tfae`: for `M N` finitely gener
ated
module over Noetherian ring `R` and ideal `I` satisfying `IM < M` and `Supp N = 
V(I)`,
if `Ext N M i = 0` for all `i < n`,
then there exists an `M`-regular sequence of length `n` contained in `I`.
-/
lemma exists_isRegular_of_exists_subsingleton_ext [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (N : ModuleCat.{v} R) [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    have : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    obtain ⟨x, mem_ann, hx⟩ := subsingleton_linearMap_iff.mp this
    -- take a power of it to make `xᵏ` fall into `I`
    obtain ⟨k, hk⟩ := le_of_le_of_eq Ideal.le_radical h_supp mem_ann
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have h_ext' : ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i) := by
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext i (by omega))
      have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext (i + 1) (by omega))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    obtain ⟨rs, len, mem, reg⟩ := ih (ModuleCat.of R (QuotSMulTop (x ^ k) M))
      (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hk smul_lt.ne).lt_top h_ext'
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

/-- The implication `(4) → (1)` of `exists_isRegular_tfae`: for `M N` finitely generated
module over Noetherian ring `R` and ideal `I` satisfying `IM < M` and `Supp N ⊆ V(I)`,
if there is an `M`-regular sequence `rs` contained in `I`,
then `Ext N M i = 0` for all `i < rs.length`. -/
/-
**ModuleCat.subsingleton_ext_of_exists_isRegular** 是 Mathlib 中的一个引理，位于命名空间 `Modu
leCat`。
形式化陈述：subsingleton_ext_of_exists_isRegular [Small.{v} R] [IsNoetherianRing R] (I
 : Ideal R) (N : ModuleCat.{v} R) [Nfin : Module.Finite R N] (Nsupp : Module.sup
port R N subseteq PrimeSpectrum.zeroLocus I) (M : ModuleCat.{v} R) [Module.Finit
e R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) (rs : List R) (mem : forall r in 
rs, r in I) (reg : IsRegular M rs) : forall i < rs.length, Subsingleton (Ext N M
 i)
参数：I : Ideal R；N : ModuleCat.{v} R；Nsupp : Module.support R N subseteq PrimeSpec
trum.zeroLocus I；M : ModuleCat.{v} R；smul_lt : I • (⊤ : Submodule R M) < ⊤；rs : 
List R；mem : forall r in rs, r in I；reg : IsRegular M rs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `PrimeSpectrum.zeroLocus_subset_zeroLocus_iff`：zeroLocus_subset_zeroLocus
_iff (I J : Ideal R) : zeroLocus (I : Set R) subseteq zeroLocus (J : Set R) ↔ J 
<= I.radical
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsSMulRegular.subsingleton_linearMap_iff`：subsingleton_linearMap_iff [Is
NoetherianRing R] [Module.Finite R M] [Module.Finite R N] : Subsingleton (N ->ₗ[
R] M) ↔ exists r in Module.ann…
· 使用定理 `IsSMulRegular.pow`：pow (n : Nat) (ra : IsSMulRegular M a) : IsSMulRegula
r M (a ^ n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用引理 `IsSMulRegular.smulShortComplex_shortExact`：IsSMulRegular.smulShortComple
x_shortExact {r : R} (reg : IsSMulRegular M r) : (ModuleCat.smulShortComplex M r
).ShortExact where exact
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'`：covariant_sequenc
e_exact₁' : (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.postcomp X h)) (A
ddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (a…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_src`：eq_zero_of_src {X Y : C} (o
 : IsZero X) (f : X ⟶ Y) : f = 0
· 使用定理 `AddCommGrpCat.isZero_of_iff_subsingleton`：∀ {G : Type u_1} [inst : AddCo
mmGroup G], CategoryTheory.Limits.IsZero (AddCommGrpCat.of G) ↔ Subsingleton G
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `_private.Mathlib.RingTheory.Depth.Rees.0.smul_top_quotSMulTop_ne_top_of_
smul_top_ne_top`：∀ {R : Type u} [inst : CommRing R] {M : Type u_1} [inst_1 : Add
CommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R}   {r : R}, r ∈ I → I …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The implication `(4) → (1)` of `exists_isRegular_tfae`: for `M N` finitely gener
ated
module over Noetherian ring `R` and ideal `I` satisfying `IM < M` and `Supp N ⊆ 
V(I)`,
if there is an `M`-regular sequence `rs` contained in `I`,
then `Ext N M i = 0` for all `i < rs.length`.
-/
lemma subsingleton_ext_of_exists_isRegular [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] => simp at len
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      obtain ⟨k, hk⟩ := le_rad (mem a List.mem_cons_self)
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      match i with
      | 0 => -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        have : Subsingleton (N →ₗ[R] M) := subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
        exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
      | i + 1 =>
        let g := (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N
          (add_zero (i + 1))))
        -- from the (covariant) long exact sequence given by `M.smulShortComplex a`
        -- we obtain scalar multiple by `a` on `Ext N M i` is injective
        have mono_g : Mono g := by
          apply (Ext.covariant_sequence_exact₁' N reg.1.smulShortComplex_shortExact i (i + 1)
            rfl).mono_g ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr ?_).eq_zero_of_src _)
          apply ih (ModuleCat.of R (QuotSMulTop a M)) _ rs' mem.2 reg.2 len i (by omega)
          exact (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top mem.1 smul_lt.ne).lt_top
        let gk := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
          (add_zero (i + 1)))
        have mono_gk : Mono gk := by
          simp only [smulShortComplex_f_eq_smul_id, g, gk] at mono_g ⊢
          exact (Ext.postcomp_smul_id_mono_iff (a ^ k) (i + 1)).mpr <|
            ((Ext.postcomp_smul_id_mono_iff a (i + 1)).mp mono_g).pow k
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hk (i + 1)
        exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

/--
**The Rees theorem**
For any `n : ℕ`, Noetherian ring `R`, `I : Ideal R`, and finitely generated and nontrivial
`R`-module `M` satisfying `IM < M`, the following are equivalent:
* for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
* `∀ i < n, Ext (R ⧸ I) M i = 0`
* there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
* there exists a `M`-regular sequence of length `n` with every element in `I`
-/
/-
**ModuleCat.exists_isRegular_tfae** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：exists_isRegular_tfae [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n 
: Nat) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R
 M) < ⊤) : [forall N : ModuleCat.{v} R, Nontrivial N -> Module.Finite R N -> Mod
ule.support R N subseteq PrimeSpectrum.zeroLocus I -> forall i < n, Subsingleton
 (Ext N M i), forall i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I
))) M i), exists N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧ Module.supp
ort R N = PrimeSpectrum.ze
参数：I : Ideal R；n : Nat；M : ModuleCat.{v} R；smul_lt : I • (⊤ : Submodule R M) < ⊤
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `Submodule.Quotient.instSmallQuotient`：∀ {R : Type u_3} {M : Type u_4} [i
nst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} [Small.{u, u_4}…
· 使用引理 `LinearEquiv.support_eq`：LinearEquiv.support_eq (e : M ≃ₗ[R] N) : Module.
support R M = Module.support R N
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `Ideal.annihilator_quotient`：∀ {R : Type u_1} [inst : Ring R] {I : Ideal 
R} [I.IsTwoSided], Module.annihilator R (R ⧸ I) = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `instNontrivialShrink`：∀ {α : Type u} [inst : Small.{v, u} α] [Nontrivial
 α], Nontrivial (Shrink.{v, u} α)
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用引理 `ModuleCat.exists_isRegular_of_exists_subsingleton_ext`：exists_isRegular_
of_exists_subsingleton_ext [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n :
 Nat) (M : ModuleCat.{v} R) [Module.Finite …
· 使用引理 `ModuleCat.subsingleton_ext_of_exists_isRegular`：subsingleton_ext_of_exis
ts_isRegular [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (N : ModuleCat.{v}
 R) [Nfin : Module.Finite R N] (Nsup…
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
**The Rees theorem**
For any `n : ℕ`, Noetherian ring `R`, `I : Ideal R`, and finitely generated and 
nontrivial
`R`-module `M` satisfying `IM < M`, the following are equivalent:
* for any `N : ModuleCat R` finitely generated and nontrivial with support conta
ined in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
* `∀ i < n, Ext (R ⧸ I) M i = 0`
* there exists a `N : ModuleCat R` finitely generated and nontrivial with suppor
t equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
* there exists a `M`-regular sequence of length `n` with every element in `I`
-/
lemma exists_isRegular_tfae [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
      Module.support R N ⊆ PrimeSpectrum.zeroLocus I → ∀ i < n, Subsingleton (Ext N M i),
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
      ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]
  tfae_have 1 → 2 := fun h1 i hi ↦ h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    inferInstance inferInstance suppQ.subset i hi
  tfae_have 2 → 3 := fun h2 ↦ ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 → 4 := fun ⟨N, _, _, h_supp, h_ext⟩ ↦
    exists_isRegular_of_exists_subsingleton_ext I n M smul_lt N h_supp h_ext
  tfae_have 4 → 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi ↦
    subsingleton_ext_of_exists_isRegular I N Nsupp M smul_lt rs mem reg i (hi.trans_eq len.symm)
  tfae_finish

end ModuleCat

