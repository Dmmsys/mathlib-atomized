/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# Support of a module

## Main results
- `Module.support`: The support of an `R`-module as a subset of `Spec R`.
- `Module.mem_support_iff_exists_annihilator`: `p ∈ Supp M ↔ ∃ m, Ann(m) ≤ p`.
- `Module.support_eq_empty_iff`: `Supp M = ∅ ↔ M = 0`
- `Module.support_of_exact`: `Supp N = Supp M ∪ Supp P` for an exact sequence `0 → M → N → P → 0`.
- `Module.support_eq_zeroLocus`: If `M` is `R`-finite, then `Supp M = Z(Ann(M))`.
- `LocalizedModule.exists_subsingleton_away`:
  If `M` is `R`-finite and `Mₚ = 0`, then `M[1/f] = 0` for some `p ∈ D(f)`.

Also see `Mathlib/RingTheory/Spectrum/Prime/Module.lean` for other results
depending on the Zariski topology.

## TODO
- Connect to associated primes once we have them in mathlib.
- Given an `R`-algebra `f : R → A` and a finite `R`-module `M`,
  `Supp_A (A ⊗ M) = f♯ ⁻¹ Supp M` where `f♯ : Spec A → Spec R`. (stacks#0BUR)
-/

@[expose] public section

-- Basic files in `RingTheory` should avoid depending on the Zariski topology
-- See `Mathlib/RingTheory/Spectrum/Prime/Module.lean`
assert_not_exists TopologicalSpace

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}

variable (R M) in
/-- The support of a module, defined as the set of primes `p` such that `Mₚ ≠ 0`. -/
@[stacks 00L1]
/-
**Module.support** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.support : Set (PrimeSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a module, defined as the set of primes `p` such that `Mₚ ≠ 0`.
-/
def Module.support : Set (PrimeSpectrum R) :=
  { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }
/-
**Module.mem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff : p in Module.support R M ↔ Nontrivial (LocalizedMo
dule p.asIdeal.primeCompl M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.mem_support_iff :
    p ∈ Module.support R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := Iff.rfl
/-
**Module.notMem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.notMem_support_iff : p ∉ Module.support R M ↔ Subsingleton (Localiz
edModule p.asIdeal.primeCompl M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
-/
lemma Module.notMem_support_iff :
    p ∉ Module.support R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M) :=
  not_nontrivial_iff_subsingleton

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.notMem_support_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.notMem_support_iff' : p ∉ Module.support R M ↔ forall m : M, exists
 r ∉ p.asIdeal, r • m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Module.notMem_support_iff' :
    p ∉ Module.support R M ↔ ∀ m : M, ∃ r ∉ p.asIdeal, r • m = 0 := by
  simp only [notMem_support_iff, Ideal.primeCompl, LocalizedModule.subsingleton_iff,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]
/-
**Module.mem_support_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff' : p in Module.support R M ↔ exists m : M, forall r
 ∉ p.asIdeal, r • m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `Module.notMem_support_iff'`：Module.notMem_support_iff' : p ∉ Module.supp
ort R M ↔ forall m : M, exists r ∉ p.asIdeal, r • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.mem_support_iff' :
    p ∈ Module.support R M ↔ ∃ m : M, ∀ r ∉ p.asIdeal, r • m ≠ 0 := by
  rw [← @not_not (_ ∈ _), notMem_support_iff']
  push Not
  rfl
/-
**Module.mem_support_iff_exists_annihilator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff_exists_annihilator : p in Module.support R M ↔ exis
ts m : M, (R ∙ m).annihilator <= p.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.mem_support_iff'`：Module.mem_support_iff' : p in Module.support R
 M ↔ exists m : M, forall r ∉ p.asIdeal, r • m != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Module.mem_support_iff_exists_annihilator :
    p ∈ Module.support R M ↔ ∃ m : M, (R ∙ m).annihilator ≤ p.asIdeal := by
  rw [Module.mem_support_iff']
  simp_rw [not_imp_not, SetLike.le_def, Submodule.mem_annihilator_span_singleton]
/-
**Module.mem_support_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_mono {p q : PrimeSpectrum R} (H : p <= q) (hp : p in Mo
dule.support R M) : q in Module.support R M
参数：H : p <= q；hp : p in Module.support R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.mem_support_iff_exists_annihilator`：Module.mem_support_iff_exists
_annihilator : p in Module.support R M ↔ exists m : M, (R ∙ m).annihilator <= p.
asIdeal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Module.mem_support_mono {p q : PrimeSpectrum R} (H : p ≤ q) (hp : p ∈ Module.support R M) :
    q ∈ Module.support R M := by
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  exact ⟨_, hp.choose_spec.trans H⟩
/-
**Module.mem_support_iff_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff_of_span_eq_top {s : Set M} (hs : Submodule.span R s
 = ⊤) : p in Module.support R M ↔ exists m in s, (R ∙ m).annihilator <= p.asIdea
l
参数：hs : Submodule.span R s = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.notMem_support_iff`：Module.notMem_support_iff : p ∉ Module.suppor
t R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `LocalizedModule.subsingleton_iff_ker_eq_top`：subsingleton_iff_ker_eq_top
 {S : Submonoid R} : Subsingleton (LocalizedModule S M) ↔ LinearMap.ker (Localiz
edModule.mkLinearMap S M) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.mem_support_iff_exists_annihilator`：Module.mem_support_iff_exists
_annihilator : p in Module.support R M ↔ exists m : M, (R ∙ m).annihilator <= p.
asIdeal
-/
lemma Module.mem_support_iff_of_span_eq_top {s : Set M} (hs : Submodule.span R s = ⊤) :
    p ∈ Module.support R M ↔ ∃ m ∈ s, (R ∙ m).annihilator ≤ p.asIdeal := by
  constructor
  · contrapose
    rw [notMem_support_iff, LocalizedModule.subsingleton_iff_ker_eq_top, ← top_le_iff,
      ← hs, Submodule.span_le, Set.subset_def]
    simp_rw [SetLike.le_def, Submodule.mem_annihilator_span_singleton, SetLike.mem_coe,
      LocalizedModule.mem_ker_mkLinearMap_iff]
    push Not
    simp_rw [and_comm]
    exact id
  · intro ⟨m, _, hm⟩
    exact mem_support_iff_exists_annihilator.mpr ⟨m, hm⟩
/-
**Module.annihilator_le_of_mem_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.annihilator_le_of_mem_support (hp : p in Module.support R M) : Modu
le.annihilator R M <= p.asIdeal
参数：hp : p in Module.support R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.mem_support_iff_exists_annihilator`：Module.mem_support_iff_exists
_annihilator : p in Module.support R M ↔ exists m : M, (R ∙ m).annihilator <= p.
asIdeal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearMap.annihilator_le_of_injective`：LinearMap.annihilator_le_of_injec
tive (f : M ->ₗ[R] M') (hf : Function.Injective f) : Module.annihilator R M' <= 
Module.annihilator R M
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma Module.annihilator_le_of_mem_support (hp : p ∈ Module.support R M) :
    Module.annihilator R M ≤ p.asIdeal := by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
  exact le_trans ((Submodule.subtype _).annihilator_le_of_injective Subtype.val_injective) hm
/-
**LocalizedModule.subsingleton_iff_support_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.subsingleton_iff_support_subset {f : R} : Subsingleton (Lo
calizedModule.Away f M) ↔ Module.support R M subseteq PrimeSpectrum.zeroLocus {f
}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.subsingleton_iff`：subsingleton_iff {S : Submonoid R} : S
ubsingleton (LocalizedModule S M) ↔ forall m : M, exists r in S, r • m = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.mem_support_iff_exists_annihilator`：Module.mem_support_iff_exists
_annihilator : p in Module.support R M ↔ exists m : M, (R ∙ m).annihilator <= p.
asIdeal
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_annihilator_span_singleton`：mem_annihilator_span_singleton
 (g : M) (r : R) : r in (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `Submodule.annihilator_eq_top_iff`：annihilator_eq_top_iff : N.annihilator
 = ⊤ ↔ N = ⊥
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma LocalizedModule.subsingleton_iff_support_subset {f : R} :
    Subsingleton (LocalizedModule.Away f M) ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus {f} := by
  rw [LocalizedModule.subsingleton_iff]
  constructor
  · rintro H x hx' f rfl
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hx'
    obtain ⟨_, ⟨n, rfl⟩, e⟩ := H m
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
      (hm ((Submodule.mem_annihilator_span_singleton _ _).mpr e))
  · intro H m
    by_cases h : (Submodule.span R {m}).annihilator = ⊤
    · rw [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] at h
      exact ⟨1, one_mem _, by simpa using h⟩
    obtain ⟨n, hn⟩ : f ∈ (Submodule.span R {m}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro p ⟨hp, hp'⟩
      simpa using H (Module.mem_support_iff_exists_annihilator (p := ⟨p, hp'⟩).mpr ⟨_, hp⟩)
    exact ⟨_, ⟨n, rfl⟩, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩
/-
**Module.support_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_eq_empty_iff : Module.support R M = ∅ ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_one`：zeroLocus_singleton_one : zeroLoc
us ({1} : Set R) = ∅
· 使用引理 `LocalizedModule.subsingleton_iff_support_subset`：LocalizedModule.subsing
leton_iff_support_subset {f : R} : Subsingleton (LocalizedModule.Away f M) ↔ Mod
ule.support R M subseteq PrimeSpectru…
· 使用引理 `LocalizedModule.subsingleton_iff`：subsingleton_iff {S : Submonoid R} : S
ubsingleton (LocalizedModule S M) ↔ forall m : M, exists r in S, r • m = 0
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Submonoid.powers_one`：powers_one : powers (1 : M) = ⊥
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Module.support_eq_empty_iff :
    Module.support R M = ∅ ↔ Subsingleton M := by
  rw [← Set.subset_empty_iff, ← PrimeSpectrum.zeroLocus_singleton_one,
    ← LocalizedModule.subsingleton_iff_support_subset, LocalizedModule.subsingleton_iff,
    subsingleton_iff_forall_eq 0]
  simp only [Submonoid.powers_one, Submonoid.mem_bot, exists_eq_left, one_smul]
/-
**Module.nonempty_support_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.nonempty_support_iff : (Module.support R M).Nonempty ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Module.support_eq_empty_iff`：Module.support_eq_empty_iff : Module.suppor
t R M = ∅ ↔ Subsingleton M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.nonempty_support_iff :
    (Module.support R M).Nonempty ↔ Nontrivial M := by
  rw [Set.nonempty_iff_ne_empty, ne_eq,
    Module.support_eq_empty_iff, ← not_subsingleton_iff_nontrivial]
/-
**Module.nonempty_support_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.nonempty_support_of_nontrivial [Nontrivial M] : (Module.support R M
).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.nonempty_support_iff`：Module.nonempty_support_iff : (Module.suppo
rt R M).Nonempty ↔ Nontrivial M
-/
lemma Module.nonempty_support_of_nontrivial [Nontrivial M] : (Module.support R M).Nonempty :=
  Module.nonempty_support_iff.mpr ‹_›
/-
**Module.support_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_eq_empty [Subsingleton M] : Module.support R M = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.support_eq_empty_iff`：Module.support_eq_empty_iff : Module.suppor
t R M = ∅ ↔ Subsingleton M
-/
lemma Module.support_eq_empty [Subsingleton M] :
    Module.support R M = ∅ :=
  Module.support_eq_empty_iff.mpr ‹_›
/-
**Module.support_of_algebra** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_of_algebra {A : Type*} [Ring A] [Algebra R A] : Module.supp
ort R A = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R A))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
lemma Module.support_of_algebra {A : Type*} [Ring A] [Algebra R A] :
    Module.support R A = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R A)) := by
  ext p
  simp only [mem_support_iff', ne_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun ⟨m, hm⟩ x hx ↦ not_not.mp fun hx' ↦ ?_, fun H ↦ ⟨1, fun r hr e ↦ ?_⟩⟩
  · simpa [Algebra.smul_def, (show _ = _ from hx)] using hm _ hx'
  · exact hr (H ((Algebra.algebraMap_eq_smul_one _).trans e))
/-
**Module.support_of_noZeroSMulDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_of_noZeroSMulDivisors [IsDomain R] [IsTorsionFree R M] [Non
trivial M] : Module.support R M = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Module.support_of_noZeroSMulDivisors [IsDomain R] [IsTorsionFree R M] [Nontrivial M] :
    Module.support R M = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_support_iff', ne_eq, smul_eq_zero, not_or]
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact fun p ↦ ⟨x, fun r hr ↦ ⟨fun e ↦ hr (e ▸ p.asIdeal.zero_mem), hx⟩⟩

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] N) (g : N →ₗ[R] P)

@[stacks 00L3 "(2)"]
/-
**Module.support_subset_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_subset_of_injective (hf : Function.Injective f) : Module.su
pport R M subseteq Module.support R N
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
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
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
lemma Module.support_subset_of_injective (hf : Function.Injective f) :
    Module.support R M ⊆ Module.support R N := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  exact ⟨f m, fun r hr ↦ by simpa using hf.ne (hm r hr)⟩

@[stacks 00L3 "(3)"]
/-
**Module.support_subset_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_subset_of_surjective (hf : Function.Surjective f) : Module.
support R N subseteq Module.support R M
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
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
-/
lemma Module.support_subset_of_surjective (hf : Function.Surjective f) :
    Module.support R N ⊆ Module.support R M := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  obtain ⟨m, rfl⟩ := hf m
  exact ⟨m, fun r hr e ↦ hm r hr (by simpa using congr(f $e))⟩

variable {f g} in
/-- Given an exact sequence `0 → M → N → P → 0` of `R`-modules, `Supp N = Supp M ∪ Supp P`. -/
@[stacks 00L3 "(4)"]
/-
**Module.support_of_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_of_exact (h : Function.Exact f g) (hf : Function.Injective 
f) (hg : Function.Surjective g) : Module.support R N = Module.support R M union 
Module.support R P
参数：h : Function.Exact f g；hf : Function.Injective f；hg : Function.Surjective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
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
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用引理 `Module.support_subset_of_injective`：Module.support_subset_of_injective (
hf : Function.Injective f) : Module.support R M subseteq Module.support R N
· 使用引理 `Module.support_subset_of_surjective`：Module.support_subset_of_surjective
 (hf : Function.Surjective f) : Module.support R N subseteq Module.support R M

--- 原说明 ---
Given an exact sequence `0 → M → N → P → 0` of `R`-modules, `Supp N = Supp M ∪ S
upp P`.
-/
lemma Module.support_of_exact (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.support R N = Module.support R M ∪ Module.support R P := by
  refine subset_antisymm ?_ (Set.union_subset (Module.support_subset_of_injective f hf)
    (Module.support_subset_of_surjective g hg))
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, notMem_support_iff']
  intro H₁ H₂ m
  obtain ⟨r, hr, e₁⟩ := H₂ (g m)
  rw [← map_smul, h] at e₁
  obtain ⟨m', hm'⟩ := e₁
  obtain ⟨s, hs, e₁⟩ := H₁ m'
  exact ⟨_, x.asIdeal.primeCompl.mul_mem hs hr, by rw [mul_smul, ← hm', ← map_smul, e₁, map_zero]⟩
/-
**LinearEquiv.support_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.support_eq (e : M ≃ₗ[R] N) : Module.support R M = Module.suppo
rt R N
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Module.support_subset_of_injective`：Module.support_subset_of_injective (
hf : Function.Injective f) : Module.support R M subseteq Module.support R N
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用引理 `Module.support_subset_of_surjective`：Module.support_subset_of_surjective
 (hf : Function.Surjective f) : Module.support R N subseteq Module.support R M
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
lemma LinearEquiv.support_eq (e : M ≃ₗ[R] N) :
    Module.support R M = Module.support R N :=
  (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
    (Module.support_subset_of_surjective e.toLinearMap e.surjective)

section Finite

variable [Module.Finite R M]

open PrimeSpectrum

/-
**Module.mem_support_iff_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff_of_finite : p in Module.support R M ↔ Module.annihi
lator R M <= p.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.annihilator_le_of_mem_support`：Module.annihilator_le_of_mem_suppo
rt (hp : p in Module.support R M) : Module.annihilator R M <= p.asIdeal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.mem_support_iff_of_span_eq_top`：Module.mem_support_iff_of_span_eq
_top {s : Set M} (hs : Submodule.span R s = ⊤) : p in Module.support R M ↔ exist
s m in s, (R ∙ m).annihilat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.annihilator_top`：annihilator_top : (⊤ : Submodule R M).annihil
ator = Module.annihilator R M
· 使用定理 `Submodule.mem_annihilator_span`：mem_annihilator_span (s : Set M) (r : R)
 : r in (Submodule.span R s).annihilator ↔ forall n : s, r • (n : M) = 0
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Submonoid.prod_mem`：prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M
) {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c i
n t, f c…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma Module.mem_support_iff_of_finite :
    p ∈ Module.support R M ↔ Module.annihilator R M ≤ p.asIdeal := by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  refine ⟨annihilator_le_of_mem_support, fun H ↦ (mem_support_iff_of_span_eq_top hs).mpr ?_⟩
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton] at H ⊢
  contrapose! H
  choose x hx hx' using Subtype.forall'.mp H
  refine ⟨s.attach.prod x, ?_, ?_⟩
  · rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x (Finset.mem_attach _ m)
    rw [hk, mul_comm, mul_smul, hx, smul_zero]
  · exact p.asIdeal.primeCompl.prod_mem (fun x _ ↦ hx' x)

/-- If `M` is `R`-finite, then `Supp M = Z(Ann(M))`. -/
@[stacks 00L2]
/-
**Module.support_eq_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_eq_zeroLocus : Module.support R M = zeroLocus (Module.annih
ilator R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Module.mem_support_iff_of_finite`：Module.mem_support_iff_of_finite : p i
n Module.support R M ↔ Module.annihilator R M <= p.asIdeal

--- 原说明 ---
If `M` is `R`-finite, then `Supp M = Z(Ann(M))`.
-/
lemma Module.support_eq_zeroLocus :
    Module.support R M = zeroLocus (Module.annihilator R M) :=
  Set.ext fun _ ↦ mem_support_iff_of_finite

/-- If `M` is a finite module such that `Mₚ = 0` for some `p`,
then `M[1/f] = 0` for some `p ∈ D(f)`. -/
/-
**LocalizedModule.exists_subsingleton_away** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.exists_subsingleton_away (p : Ideal R) [p.IsPrime] [Subsin
gleton (LocalizedModule p.primeCompl M)] : exists f ∉ p, Subsingleton (Localized
Module.Away f M)
参数：p : Ideal R；LocalizedModule p.primeCompl M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.compl_iInter₂`：compl_iInter₂ (s : forall i, κ i -> Set α) : (⋂ (i) (
j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion₂`：zeroLocus_iUnion₂ {ι : Sort*} {κ : (i :
 ι) -> Sort*} (s : forall i, κ i -> Set R) : zeroLocus (⋃ (i) (j), s i j) = ⋂ (i
) (j), zeroLocus (s i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LocalizedModule.subsingleton_iff`：subsingleton_iff {S : Submonoid R} : S
ubsingleton (LocalizedModule S M) ↔ forall m : M, exists r in S, r • m = 0
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0

--- 原说明 ---
If `M` is a finite module such that `Mₚ = 0` for some `p`,
then `M[1/f] = 0` for some `p ∈ D(f)`.
-/
lemma LocalizedModule.exists_subsingleton_away (p : Ideal R) [p.IsPrime]
    [Subsingleton (LocalizedModule p.primeCompl M)] :
    ∃ f ∉ p, Subsingleton (LocalizedModule.Away f M) := by
  have : ⟨p, inferInstance⟩ ∈ (Module.support R M)ᶜ := by
    simpa [Module.notMem_support_iff]
  rw [Module.support_eq_zeroLocus, ← Set.biUnion_of_singleton (Module.annihilator R M : Set R),
    PrimeSpectrum.zeroLocus_iUnion₂, Set.compl_iInter₂, Set.mem_iUnion₂] at this
  obtain ⟨f, hf, hf'⟩ := this
  exact ⟨f, by simpa using hf', subsingleton_iff.mpr
    fun m ↦ ⟨f, Submonoid.mem_powers f, Module.mem_annihilator.mp hf _⟩⟩
/-
**IsLocalizedModule.exists_subsingleton_away** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.exists_subsingleton_away {M' : Type*} [AddCommMonoid M']
 [Module R M'] (l : M ->ₗ[R] M') (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.
primeCompl l] [Subsingleton M'] : exists f ∉ p, Subsingleton (LocalizedModule.Aw
ay f M)
参数：l : M ->ₗ[R] M'；p : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用引理 `LocalizedModule.exists_subsingleton_away`：LocalizedModule.exists_subsing
leton_away (p : Ideal R) [p.IsPrime] [Subsingleton (LocalizedModule p.primeCompl
 M)] : exists f ∉ p, Subsingle…
-/
lemma IsLocalizedModule.exists_subsingleton_away {M' : Type*} [AddCommMonoid M'] [Module R M']
    (l : M →ₗ[R] M') (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.primeCompl l]
    [Subsingleton M'] :
    ∃ f ∉ p, Subsingleton (LocalizedModule.Away f M) := by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  exact LocalizedModule.exists_subsingleton_away p
/-
**Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective*
* 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surject
ive (p : Ideal R) [p.IsPrime] (φ : N ->ₗ[R] M) (hφ : Function.Surjective (Locali
zedModule.map p.primeCompl φ)) : exists a ∉ p, Function.Surjective (LocalizedMod
ule.map (Submonoid.powers a) φ)
参数：p : Ideal R；φ : N ->ₗ[R] M；hφ : Function.Surjective (LocalizedModule.map p.pr
imeCompl φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker`：loca
lizedMap_surjective_iff_subsingleton_localized_coker {R M N : Type*} [CommRing R
] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module…
· 使用引理 `LocalizedModule.exists_subsingleton_away`：LocalizedModule.exists_subsing
leton_away (p : Ideal R) [p.IsPrime] [Subsingleton (LocalizedModule p.primeCompl
 M)] : exists f ∉ p, Subsingle…
-/
lemma Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective (p : Ideal R)
    [p.IsPrime] (φ : N →ₗ[R] M) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

/-- `Supp(M/IM) = Supp(M) ∩ Z(I)`. -/
@[stacks 00L3 "(1)"]
/-
**Module.support_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.support_quotient (I : Ideal R) : support R (M ⧸ (I • ⊤ : Submodule 
R M)) = support R M inter zeroLocus I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用引理 `Module.support_subset_of_surjective`：Module.support_subset_of_surjective
 (hf : Function.Surjective f) : Module.support R N subseteq Module.support R M
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `PrimeSpectrum.zeroLocus_anti_mono_ideal`：zeroLocus_anti_mono_ideal {s t 
: Ideal R} (h : s <= t) : zeroLocus (t : Set R) subseteq zeroLocus (s : Set R)
· 使用定理 `Submodule.annihilator_quotient`：annihilator_quotient : Module.annihilato
r R (M ⧸ N) = N.colon Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_colon`：mem_colon {r} : r in N.colon S ↔ forall s in S, r •
 s in N
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Module.mem_support_iff`：Module.mem_support_iff : p in Module.support R M
 ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)
· 使用定理 `Submodule.localized.eq_1`：∀ {R : Type u_1} {M : Type u_3} [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submono
id R) (M' : Su…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Submodule.localized'_smul`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3
} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : A
ddCommMonoid M]…
· 使用定理 `Ideal.localized'_eq_map`：∀ {R : Type u_1} (S : Type u_2) [inst : CommSem
iring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (p : Submonoid R) [i
nst_3 : IsLoc…
· 使用定理 `Submodule.localized'_top`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用引理 `Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`：top_ne_ideal_smu
l_of_le_jacobson_annihilator [Nontrivial M] [Module.Finite R M] {I} (h : I <= (M
odule.annihilator R M).jacobson) : (⊤ : Subm…
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`Supp(M/IM) = Supp(M) ∩ Z(I)`.
-/
theorem Module.support_quotient (I : Ideal R) :
    support R (M ⧸ (I • ⊤ : Submodule R M)) = support R M ∩ zeroLocus I := by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx ↦ Submodule.mem_colon.mpr fun p hp ↦ Submodule.smul_mem_smul hx hp
  · rintro p ⟨hp₁, hp₂⟩
    rw [Module.mem_support_iff] at hp₁ ⊢
    let Rₚ := Localization.AtPrime p.asIdeal
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    set Mₚ' := LocalizedModule p.asIdeal.primeCompl (M ⧸ (I • ⊤ : Submodule R M))
    let Mₚ'' := Mₚ ⧸ I.map (algebraMap R Rₚ) • (⊤ : Submodule Rₚ Mₚ)
    let e : Mₚ' ≃ₗ[Rₚ] Mₚ'' := (localizedQuotientEquiv _ _).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by rw [Submodule.localized,
        Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top])
    have : Nontrivial Mₚ'' := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine trans ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hp₂
    exact e.nontrivial

open scoped Pointwise in
@[simp]
/-
**Module.support_quotSMulTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.support_quotSMulTop (x : R) : support R (QuotSMulTop x M) = support
 R M inter zeroLocus {x}
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LinearEquiv.support_eq`：LinearEquiv.support_eq (e : M ≃ₗ[R] N) : Module.
support R M = Module.support R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ideal_span_singleton_smul`：ideal_span_singleton_smul (r : R) (
N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N
· 使用定理 `Module.support_quotient`：Module.support_quotient (I : Ideal R) : support
 R (M ⧸ (I • ⊤ : Submodule R M)) = support R M inter zeroLocus I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
-/
theorem Module.support_quotSMulTop (x : R) :
    support R (QuotSMulTop x M) = support R M ∩ zeroLocus {x} :=
  (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
    ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm |>.support_eq.trans <|
      (support_quotient _).trans <| by rw [zeroLocus_span]

end Finite

