/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support

/-!

# Subsets of prime spectra related to modules

## Main results

- `LocalizedModule.subsingleton_iff_disjoint` : `M[1/f] = 0 ↔ D(f) ∩ Supp M = 0`.
- `Module.isClosed_support` : If `M` is a finite `R`-module, then `Supp M` is closed.

## TODO
- If `M` is finitely presented, the complement of `Supp M` is quasi-compact. (stacks#051B)

-/

public section

variable {R A M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A] [Module A M]

variable (R M) in
/-
**IsLocalRing.closedPoint_mem_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.closedPoint_mem_support [IsLocalRing R] [Nontrivial M] : IsLoc
alRing.closedPoint R in Module.support R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.nonempty_support_iff`：Module.nonempty_support_iff : (Module.suppo
rt R M).Nonempty ↔ Nontrivial M
· 使用引理 `Module.mem_support_mono`：Module.mem_support_mono {p q : PrimeSpectrum R}
 (H : p <= q) (hp : p in Module.support R M) : q in Module.support R M
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma IsLocalRing.closedPoint_mem_support [IsLocalRing R] [Nontrivial M] :
    IsLocalRing.closedPoint R ∈ Module.support R M := by
  obtain ⟨p, hp⟩ := (Module.nonempty_support_iff (R := R)).mpr ‹_›
  exact Module.mem_support_mono le_top hp

/-- `M[1/f] = 0` if and only if `D(f) ∩ Supp M = 0`. -/
/-
**LocalizedModule.subsingleton_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.subsingleton_iff_disjoint {f : R} : Subsingleton (Localize
dModule.Away f M) ↔ Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.subsingleton_iff_support_subset`：LocalizedModule.subsing
leton_iff_support_subset {f : R} : Subsingleton (LocalizedModule.Away f M) ↔ Mod
ule.support R M subseteq PrimeSpectru…
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `disjoint_compl_left_iff`：disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= 
x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`M[1/f] = 0` if and only if `D(f) ∩ Supp M = 0`.
-/
lemma LocalizedModule.subsingleton_iff_disjoint {f : R} :
    Subsingleton (LocalizedModule.Away f M) ↔
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R M) := by
  rw [subsingleton_iff_support_subset, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    disjoint_compl_left_iff]
/-
**Module.stableUnderSpecialization_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.stableUnderSpecialization_support : StableUnderSpecialization (Modu
le.support R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.mem_support_mono`：Module.mem_support_mono {p q : PrimeSpectrum R}
 (H : p <= q) (hp : p in Module.support R M) : q in Module.support R M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
-/
lemma Module.stableUnderSpecialization_support : StableUnderSpecialization (Module.support R M) :=
  fun x y e ↦ mem_support_mono <| (PrimeSpectrum.le_iff_specializes x y).mpr e
/-
**Module.isClosed_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.isClosed_support [Module.Finite R M] : IsClosed (Module.support R M
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
-/
lemma Module.isClosed_support [Module.Finite R M] :
    IsClosed (Module.support R M) := by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus
/-
**Module.support_subset_preimage_comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.support_subset_preimage_comap [IsScalarTower R A M] : Module.suppor
t A M subseteq PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
lemma Module.support_subset_preimage_comap [IsScalarTower R A M] :
    Module.support A M ⊆ PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M := by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e ↦ hm _ (by simpa)⟩
