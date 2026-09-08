/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Normalizer

/-!
# Engel's theorem

This file contains a proof of Engel's theorem providing necessary and sufficient conditions for Lie
algebras and Lie modules to be nilpotent.

The key result `LieModule.isNilpotent_iff_forall` says that if `M` is a Lie module of a
Noetherian Lie algebra `L`, then `M` is nilpotent iff the image of `L → End(M)` consists of
nilpotent elements. In the special case that we have the adjoint representation `M = L`, this says
that a Lie algebra is nilpotent iff `ad x : End(L)` is nilpotent for all `x : L`.

Engel's theorem is true for any coefficients (i.e., it is really a theorem about Lie rings) and so
we work with coefficients in any commutative ring `R` throughout.

On the other hand, Engel's theorem is not true for infinite-dimensional Lie algebras and so a
finite-dimensionality assumption is required. We prove the theorem subject to the assumption
that the Lie algebra is Noetherian as an `R`-module, though actually we only need the slightly
weaker property that the relation `>` is well-founded on the complete lattice of Lie subalgebras.

## Remarks about the proof

Engel's theorem is usually proved in the special case that the coefficients are a field, and uses
an inductive argument on the dimension of the Lie algebra. One begins by choosing either a maximal
proper Lie subalgebra (in some proofs) or a maximal nilpotent Lie subalgebra (in other proofs, at
the cost of obtaining a weaker end result).

Since we work with general coefficients, we cannot induct on dimension and an alternate approach
must be taken. The key ingredient is the concept of nilpotency, not just for Lie algebras, but for
Lie modules. Using this concept, we define an _Engelian Lie algebra_ `LieAlgebra.IsEngelian` to
be one for which a Lie module is nilpotent whenever the action consists of nilpotent endomorphisms.
The argument then proceeds by selecting a maximal Engelian Lie subalgebra and showing that it cannot
be proper.

The first part of the traditional statement of Engel's theorem consists of the statement that if `M`
is a non-trivial `R`-module and `L ⊆ End(M)` is a finite-dimensional Lie subalgebra of nilpotent
elements, then there exists a non-zero element `m : M` that is annihilated by every element of `L`.
This follows trivially from the result established here `LieModule.isNilpotent_iff_forall`, that
`M` is a nilpotent Lie module over `L`, since the last non-zero term in the lower central series
will consist of such elements `m` (see: `LieModule.nontrivial_max_triv_of_isNilpotent`). It seems
that this result has not previously been established at this level of generality.

The second part of the traditional statement of Engel's theorem concerns nilpotency of the Lie
algebra and a proof of this for general coefficients appeared in the literature as long ago
[as 1937](zorn1937). This also follows trivially from `LieModule.isNilpotent_iff_forall` simply by
taking `M = L`.

It is pleasing that the two parts of the traditional statements of Engel's theorem are thus unified
into a single statement about nilpotency of Lie modules. This is not usually emphasised.

## Main definitions

  * `LieAlgebra.IsEngelian`
  * `LieAlgebra.isEngelian_of_isNoetherian`
  * `LieModule.isNilpotent_iff_forall`
  * `LieAlgebra.isNilpotent_iff_forall`

-/

@[expose] public section


universe u₁ u₂ u₃ u₄

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubmodule

open LieModule

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)
include hxI

/-
**LieSubmodule.exists_smul_add_of_span_sup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Submodule`。
形式化陈述：exists_smul_add_of_span_sup_eq_top (y : L) : exists t : R, exists z in I, 
y = t • x + z
参数：y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_smul_add_of_span_sup_eq_top (y : L) : ∃ t : R, ∃ z ∈ I, y = t • x + z := by
  have hy : y ∈ (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩
/-
**LieSubmodule.lie_top_eq_of_span_sup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmo
dule`。
形式化陈述：lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) : (↑⁅(⊤ : LieIdeal 
R L), N⁆ : Submodule R M) = (N : Submodule R M).map (toEnd R L M x) ⊔ (↑⁅I, N⁆ :
 Submodule R M)
参数：N : LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.sup_span`：sup_span : p ⊔ span R s = span R (p union s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LieSubmodule.exists_smul_add_of_span_sup_eq_top`：exists_smul_add_of_span
_sup_eq_top (y : L) : exists t : R, exists z in I, y = t • x + z
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.smul_mem'`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (self : Submodule R M) (c
 : R) {x …
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) :
    (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) =
      (N : Submodule R M).map (toEnd R L M x) ⊔ (↑⁅I, N⁆ : Submodule R M) := by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n ∈ N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_span_sup_eq_top hxI y
    simp only [SetLike.mem_coe, Submodule.span_union, Submodule.mem_sup]
    exact
      ⟨t • ⁅x, n⁆, Submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩, ⁅z, n⁆,
        Submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩
  · rcases hz with (⟨m, hm, rfl⟩ | ⟨y, -, m, hm, rfl⟩)
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩]
/-
**LieSubmodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `LieSubmodule`。
形式化陈述：lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : Nat} (hxn : toEnd R L 
M x ^ n = 0) (hIM : lowerCentralSeries R L M i <= I.lcs M j) : lowerCentralSerie
s R L M (i + n) <= I.lcs M (j + 1)
参数：hxn : toEnd R L M x ^ n = 0；hIM : lowerCentralSeries R L M i <= I.lcs M j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
· 使用定理 `LieIdeal.lcs_succ`：lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `LieSubmodule.lie_top_eq_of_span_sup_eq_top`：lie_top_eq_of_span_sup_eq_to
p (N : LieSubmodule R L M) : (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) = (N : S
ubmodule R M).map (toEnd R L M x…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LieSubmodule.coe_map_toEnd_le`：coe_map_toEnd_le : (N : Submodule R M).ma
p (LieModule.toEnd R L M x) <= N
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_zero`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : ℕ}
    (hxn : toEnd R L M x ^ n = 0) (hIM : lowerCentralSeries R L M i ≤ I.lcs M j) :
    lowerCentralSeries R L M (i + n) ≤ I.lcs M (j + 1) := by
  suffices
    ∀ l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) ≤
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using! this n
  intro l
  induction l with
  | zero =>
    simp only [add_zero, LieIdeal.lcs_succ, pow_zero, Module.End.one_eq_id,
      Submodule.map_id]
    exact le_sup_of_le_left hIM
  | succ l ih =>
    simp only [LieIdeal.lcs_succ, i.add_succ l, lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff]
    refine ⟨(Submodule.map_mono ih).trans ?_, le_sup_of_le_right ?_⟩
    · rw [Submodule.map_sup, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← pow_succ', ←
        I.lcs_succ]
      grw [coe_map_toEnd_le]
    · norm_cast
      gcongr
      exact le_trans (antitone_lowerCentralSeries R L M le_self_add) hIM
/-
**LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop** 是 Mathlib 中的一个定理，位于命名空间 `L
ieSubmodule`。
形式化陈述：isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x) 
(hIM : IsNilpotent I M) : IsNilpotent L M
参数：hnp : IsNilpotent <| toEnd R L M x；hIM : IsNilpotent I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.coe_lcs_eq`：coe_lcs_eq [LieModule R L M] : LieSubmodule.toSubmo
dule (I.lcs M k) = lowerCentralSeries R I M k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LieSubmodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top`：lcs_le_lcs_of_i
s_nilpotent_span_sup_eq_top {n i j : Nat} (hxn : toEnd R L M x ^ n = 0) (hIM : l
owerCentralSeries R L M i <= I.lcs M j) : low…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
-/
theorem isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x)
    (hIM : IsNilpotent I M) : IsNilpotent L M := by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices ∀ l, lowerCentralSeries R L M (l * n) ≤ I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [hk'] using this k
  intro l
  induction l with
  | zero => simp
  | succ l ih => exact (l.succ_mul n).symm ▸ lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih

end LieSubmodule

section LieAlgebra

open LieModule hiding IsNilpotent

variable (R L)

/-- A Lie algebra `L` is said to be Engelian if a sufficient condition for any `L`-Lie module `M` to
be nilpotent is that the image of the map `L → End(M)` consists of nilpotent elements.

Engel's theorem `LieAlgebra.isEngelian_of_isNoetherian` states that any Noetherian Lie algebra is
Engelian. -/
/-
**LieAlgebra.IsEngelian** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieAlgebra.IsEngelian : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra `L` is said to be Engelian if a sufficient condition for any `L`-L
ie module `M` to
be nilpotent is that the image of the map `L → End(M)` consists of nilpotent ele
ments.

Engel's theorem `LieAlgebra.isEngelian_of_isNoetherian` states that any Noetheri
an Lie algebra is
Engelian.
-/
def LieAlgebra.IsEngelian : Prop :=
  ∀ (M : Type u₄) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
    (∀ x : L, IsNilpotent (toEnd R L M x)) → LieModule.IsNilpotent L M

variable {R L}
/-
**LieAlgebra.isEngelian_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEnge
lian R L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.trivial_lie_oper_zero`：LieSubmodule.trivial_lie_oper_zero [
LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp
/-
**Function.Surjective.isEngelian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.isEngelian {f : L ->ₗ⁅R⁆ L₂} (hf : Function.Surjective
 f) (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L) : LieAlgebra.IsEngelian.{u₁, u₃
, u₄} R L₂
参数：hf : Function.Surjective f；h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.compLieHom`：LieModule.compLieHom [Module R M] [LieModule R L₂ 
M] : @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Function.Surjective.lieModuleIsNilpotent`：Function.Surjective.lieModuleI
sNilpotent [IsNilpotent L M] : IsNilpotent L₂ M₂
-/
theorem Function.Surjective.isEngelian {f : L →ₗ⁅R⁆ L₂} (hf : Function.Surjective f)
    (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L) : LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ := by
  intro M _i1 _i2 _i3 _i4 h'
  let : LieRingModule L M := LieRingModule.compLieHom M f
  let : LieModule R L M := compLieHom M f
  have hnp : ∀ x, IsNilpotent (toEnd R L M x) := fun x => h' (f x)
  have surj_id : Function.Surjective (LinearMap.id : M →ₗ[R] M) := Function.surjective_id
  have : LieModule.IsNilpotent L M := h M hnp
  apply hf.lieModuleIsNilpotent _ surj_id
  aesop
/-
**LieEquiv.isEngelian_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) : LieAlgebra.IsEngelian.{u₁, u₂, 
u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂
参数：e : L ≃ₗ⁅R⁆ L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isEngelian`：Function.Surjective.isEngelian {f : L ->
ₗ⁅R⁆ L₂} (hf : Function.Surjective f) (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R 
L) : LieAlgebra.IsEn…
· 使用定理 `LieEquiv.surjective`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : 
CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R
 L₁] [ins…
-/
theorem LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
    LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ :=
  ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩
/-
**LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgeb
ra R L} (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) 
: exists (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K <
 K'
参数：hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K；hK₂ : K < K.normalizer。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubalgebra.lie_mem_sup_of_mem_normalizer`：lie_mem_sup_of_mem_normaliz
er {x y z : L} (hx : x in H.normalizer) (hy : y in R ∙ x ⊔ ↑H) (hz : z in R ∙ x 
⊔ ↑H) : ⁅y, z⁆ in R ∙ x ⊔ ↑H
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubalgebra.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (
K : Submodule R L) <= K' ↔ K <= K'
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer`：exists_nested_lieI
deal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H <= K) (h₂ : K <= H.normaliz
er) : exists I : LieIdeal R K, (I : LieSub…
· 使用定理 `LieIdeal.toLieSubalgebra_toSubmodule`：LieIdeal.toLieSubalgebra_toSubmodu
le (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule
.toSubmodule I
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.map_subtype_range_inclusion`：map_subtype_range_inclusion {p p'
 : Submodule R M} (h : p <= p') : map p'.subtype (range <| inclusion h) = p
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_subtype_span_singleton`：map_subtype_span_singleton {p : Su
bmodule R M} (x : p) : map p.subtype (R ∙ x) = R ∙ (x : M)
· 使用定理 `LieSubalgebra.coe_set_eq`：coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁
' : Set L) = L₂' ↔ L₁' = L₂'
· 使用定理 `LieEquiv.isEngelian_iff`：LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) : LieA
lgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂
· 使用定理 `LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop`：isNilpotentOfIsNilpot
entSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x) (hIM : IsNilpotent I M) : I
sNilpotent L M
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
-/
theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L}
    (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) :
    ∃ (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K < K' := by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x ∈ K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  have hKK' : K ≤ K' := (LieSubalgebra.toSubmodule_le_toSubmodule K K').mp le_sup_right
  have hK' : K' ≤ K.normalizer := by
    rw [← LieSubalgebra.toSubmodule_le_toSubmodule]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le
  refine ⟨K', ?_, lt_iff_le_and_ne.mpr ⟨hKK', fun contra => hx₂ (contra.symm ▸ hxK')⟩⟩
  intro M _i1 _i2 _i3 _i4 h
  obtain ⟨I, hI₁ : (I : LieSubalgebra R K') = LieSubalgebra.ofLe hKK'⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hKK' hK'
  have hI₂ : R ∙ (⟨x, hxK'⟩ : K') ⊔ LieSubmodule.toSubmodule I = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R K' I, hI₁]
    apply Submodule.map_injective_of_injective (K' : Submodule R L).injective_subtype
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
  have e : K ≃ₗ⁅R⁆ I :=
    (LieSubalgebra.equivOfLe hKK').trans
      (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI₁.symm))
  have hI₃ : LieAlgebra.IsEngelian R I := e.isEngelian_iff.mp hK₁
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ (h _) (hI₃ _ fun x => h x)

attribute [local instance] LieSubalgebra.subsingleton_bot
attribute [local instance 100] LieRing.ofAssociativeRing

/-- *Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`LieModule.nontrivial_max_triv_of_isNilpotent`, `LieModule.isNilpotent_iff_forall`,
`LieAlgebra.isNilpotent_iff_forall`. -/
/-
**LieAlgebra.isEngelian_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.isEngelian_of_isNoetherian [IsNoetherian R L] : LieAlgebra.IsEn
gelian R L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.isNilpotent_range_toEnd_iff`：isNilpotent_range_toEnd_iff : IsN
ilpotent (toEnd R L M).range M ↔ IsNilpotent L M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LieAlgebra.isEngelian_of_subsingleton`：LieAlgebra.isEngelian_of_subsingl
eton [Subsingleton L] : LieAlgebra.IsEngelian R L
· 使用定理 `LieSubalgebra.subsingleton_bot`：subsingleton_bot : Subsingleton (⊥ : Lie
Subalgebra R L)
· 使用定理 `LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer`：LieAlgebra.ex
ists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L} (hK₁ : LieA
lgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < …
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `LieSubalgebra.le_normalizer`：le_normalizer : H <= H.normalizer
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LieSubalgebra.normalizer_eq_self_iff`：normalizer_eq_self_iff : H.normali
zer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `LieAlgebra.isNilpotent_ad_of_isNilpotent`：LieAlgebra.isNilpotent_ad_of_i
sNilpotent {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) : IsNilpote
nt (LieAlgebra.ad R L x)
· 使用定理 `Module.End.IsNilpotent.mapQ`：∀ {R : Type u_1} {M : Type v} [inst : Ring 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.End R M}
 {p : Submodule R…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LieModule.nontrivial_max_triv_of_isNilpotent`：nontrivial_max_triv_of_isN
ilpotent [Nontrivial M] [IsNilpotent L M] : Nontrivial (maxTrivSubmodule R L M)
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `LieHom.surjective_rangeRestrict`：surjective_rangeRestrict : Function.Sur
jective f.rangeRestrict
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `LieModule.isNilpotent_of_top_iff`：LieModule.isNilpotent_of_top_iff : IsN
ilpotent (⊤ : LieSubalgebra R L) M ↔ IsNilpotent L M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
*Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`LieModule.nontrivial_max_triv_of_isNilpotent`, `LieModule.isNilpotent_iff_foral
l`,
`LieAlgebra.isNilpotent_iff_forall`.
-/
theorem LieAlgebra.isEngelian_of_isNoetherian [IsNoetherian R L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : ∀ y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngelian R K}
  have hs : s.Nonempty := ⟨⊥, LieAlgebra.isEngelian_of_subsingleton⟩
  suffices ⊤ ∈ s by
    rw [← isNilpotent_of_top_iff (R := R)]
    apply this M
    simp [LieSubalgebra.toEnd_eq, h]
  have : ∀ K ∈ s, K ≠ ⊤ → ∃ K' ∈ s, K < K' := by
    rintro K (hK₁ : LieAlgebra.IsEngelian R K) hK₂
    apply LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer hK₁
    apply lt_of_le_of_ne K.le_normalizer
    rw [Ne, eq_comm, K.normalizer_eq_self_iff, ← Ne, ←
      LieSubmodule.nontrivial_iff_ne_bot R K]
    have : Nontrivial (L' ⧸ K.toLieSubmodule) := Submodule.Quotient.nontrivial_iff.2 <| by simpa
    have : LieModule.IsNilpotent K (L' ⧸ K.toLieSubmodule) := by
      refine hK₁ _ fun x => ?_
      have hx := LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)
      apply Module.End.IsNilpotent.mapQ ?_ hx
      intro X HX
      simp only [LieSubalgebra.coe_toLieSubmodule, LieSubalgebra.mem_toSubmodule] at HX
      simp only [LieSubalgebra.coe_toLieSubmodule, Submodule.mem_comap, ad_apply,
        LieSubalgebra.mem_toSubmodule]
      exact LieSubalgebra.lie_mem K x.prop HX
    exact nontrivial_max_triv_of_isNilpotent R K (L' ⧸ K.toLieSubmodule)
  have _i5 : IsNoetherian R L' := by
    refine isNoetherian_of_surjective (LieHom.rangeRestrict (toEnd R L M)).toLinearMap ?_
    simp only [LinearMap.range_eq_top]
    exact LieHom.surjective_rangeRestrict (toEnd R L M)
  obtain ⟨K, hK₁, hK₂⟩ := (LieSubalgebra.wellFoundedGT_of_noetherian R L').wf.has_min s hs
  obtain rfl : K = ⊤ := by grind
  exact hK₁

/-- Engel's theorem.

See also `LieModule.isNilpotent_iff_forall'` which assumes that `M` is Noetherian instead of `L`. -/
/-
**LieModule.isNilpotent_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.isNilpotent_iff_forall [IsNoetherian R L] : LieModule.IsNilpoten
t L M ↔ forall x, _root_.IsNilpotent toEnd R L M x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.isNilpotent_toEnd_of_isNilpotent`：isNilpotent_toEnd_of_isNilpo
tent [IsNilpotent L M] (x : L) : _root_.IsNilpotent (toEnd R L M x)
· 使用定理 `LieAlgebra.isEngelian_of_isNoetherian`：LieAlgebra.isEngelian_of_isNoethe
rian [IsNoetherian R L] : LieAlgebra.IsEngelian R L

--- 原说明 ---
Engel's theorem.

See also `LieModule.isNilpotent_iff_forall'` which assumes that `M` is Noetheria
n instead of `L`.
-/
theorem LieModule.isNilpotent_iff_forall [IsNoetherian R L] :
    LieModule.IsNilpotent L M ↔ ∀ x, _root_.IsNilpotent <| toEnd R L M x :=
  ⟨fun _ ↦ isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

/-- Engel's theorem. -/
/-
**LieModule.isNilpotent_iff_forall'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.isNilpotent_iff_forall' [IsNoetherian R M] : LieModule.IsNilpote
nt L M ↔ forall x, _root_.IsNilpotent toEnd R L M x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.isNilpotent_range_toEnd_iff`：isNilpotent_range_toEnd_iff : IsN
ilpotent (toEnd R L M).range M ↔ IsNilpotent L M
· 使用定理 `LieModule.isNilpotent_iff_forall`：LieModule.isNilpotent_iff_forall [IsNo
etherian R L] : LieModule.IsNilpotent L M ↔ forall x, _root_.IsNilpotent toEnd R
 L M x
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `LieModule.toEnd_module_end`：LieModule.toEnd_module_end : LieModule.toEnd
 R (Module.End R M) M = LieHom.id
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Engel's theorem.
-/
theorem LieModule.isNilpotent_iff_forall' [IsNoetherian R M] :
    LieModule.IsNilpotent L M ↔ ∀ x, _root_.IsNilpotent <| toEnd R L M x := by
  rw [← isNilpotent_range_toEnd_iff (R := R), LieModule.isNilpotent_iff_forall (R := R)]; simp

/-- Engel's theorem. -/
/-
**LieAlgebra.isNilpotent_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] : LieRing.IsNilpotent
 L ↔ forall x, IsNilpotent LieAlgebra.ad R L x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.isNilpotent_iff_forall`：LieModule.isNilpotent_iff_forall [IsNo
etherian R L] : LieModule.IsNilpotent L M ↔ forall x, _root_.IsNilpotent toEnd R
 L M x

--- 原说明 ---
Engel's theorem.
-/
theorem LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] :
    LieRing.IsNilpotent L ↔ ∀ x, IsNilpotent <| LieAlgebra.ad R L x :=
  LieModule.isNilpotent_iff_forall

end LieAlgebra

