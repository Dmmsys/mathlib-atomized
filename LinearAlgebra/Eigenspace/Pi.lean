/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Simultaneous eigenvectors and eigenvalues for families of endomorphisms

In finite dimensions, the theory of simultaneous eigenvalues for a family of linear endomorphisms
`i ↦ f i` enjoys similar properties to that of a single endomorphism, provided the family obeys a
compatibility condition. This condition is that the maximum generalised eigenspaces of each
endomorphism are invariant under the action of all members of the family. It is trivially satisfied
for commuting endomorphisms but there are important more general situations where it also holds
(e.g., representations of nilpotent Lie algebras).

## Main definitions / results
* `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`: the simultaneous generalised
  eigenspaces of a compatible family of endomorphisms are independent.
* `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`: in finite dimensions, the
  simultaneous generalised eigenspaces of a compatible family of endomorphisms span if the same
  is true of each map individually.

-/

public section

open Function Set

namespace Module.End

variable {ι R K M : Type*} [CommRing R] [Field K] [AddCommGroup M] [Module R M] [Module K M]
  (f : ι → End R M)

/-
**Module.End.mem_iInf_maxGenEigenspace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End
`。
形式化陈述：mem_iInf_maxGenEigenspace_iff (χ : ι -> R) (m : M) : m in ⨅ i, (f i).maxGe
nEigenspace (χ i) ↔ forall j, exists k : Nat, ((f j - χ j • ↑1) ^ k) m = 0
参数：χ : ι -> R；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf_maxGenEigenspace_iff (χ : ι → R) (m : M) :
    m ∈ ⨅ i, (f i).maxGenEigenspace (χ i) ↔ ∀ j, ∃ k : ℕ, ((f j - χ j • ↑1) ^ k) m = 0 := by
  simp

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
submodule `p` which is invariant w.r.t. every `f i`, the intersection of `p` with the simultaneous
maximal generalised eigenspace (taken over all `i`), is the same as the simultaneous maximal
generalised eigenspace of the `f i` restricted to `p`. -/
/-
**Module.End._root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo** 是 Mat
hlib 中的一个引理，位于命名空间 `Module.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i 
↦ μ i`, and a
submodule `p` which is invariant w.r.t. every `f i`, the intersection of `p` wit
h the simultaneous
maximal generalised eigenspace (taken over all `i`), is the same as the simultan
eous maximal
generalised eigenspace of the `f i` restricted to `p`.
-/
lemma _root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo {μ : ι → R}
    (p : Submodule R M) (hfp : ∀ i, MapsTo (f i) p p) :
    p ⊓ ⨅ i, (f i).maxGenEigenspace (μ i) =
      (⨅ i, maxGenEigenspace ((f i).restrict (hfp i)) (μ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, p.inf_genEigenspace _ (hfp _), Submodule.map_iInf _ p.injective_subtype]

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
distinguished index `i` whose maximal generalised `μ i`-eigenspace is invariant w.r.t. every `f j`,
taking simultaneous maximal generalised eigenspaces is unaffected by first restricting to the
distinguished generalised `μ i`-eigenspace. -/
/-
**Module.End.iInf_maxGenEigenspace_restrict_map_subtype_eq** 是 Mathlib 中的一个引理，位于
命名空间 `Module.End`。
形式化陈述：iInf_maxGenEigenspace_restrict_map_subtype_eq {μ : ι -> R} (i : ι) (h : fo
rall j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGenEigenspace (μ i
))) : letI p
参数：i : ι；h : forall j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGen
Eigenspace (μ i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `Submodule.map_iInf`：map_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodul
e R M} (f : M ->ₛₗ[σ₁₂] M₂) (hf : Injective f) : (⨅ i, p i).map f = ⨅ i, (p i).m
ap f
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用引理 `Submodule.inf_iInf`：inf_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodul
e R M} (q : Submodule R M) : q ⊓ ⨅ i, p i = ⨅ i, q ⊓ p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.inf_genEigenspace`：∀ {R : Type v} {M : Type w} [inst : CommRin
g R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.End R 
M) (p : Submodule…

--- 原说明 ---
Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i 
↦ μ i`, and a
distinguished index `i` whose maximal generalised `μ i`-eigenspace is invariant 
w.r.t. every `f j`,
taking simultaneous maximal generalised eigenspaces is unaffected by first restr
icting to the
distinguished generalised `μ i`-eigenspace.
-/
lemma iInf_maxGenEigenspace_restrict_map_subtype_eq
    {μ : ι → R} (i : ι)
    (h : ∀ j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGenEigenspace (μ i))) :
    letI p := (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGenEigenspace (μ j) := by
    refine le_antisymm ?_ inf_le_right
    simpa only [le_inf_iff, le_refl, and_true] using iInf_le _ _
  rw [Submodule.map_iInf _ p.injective_subtype, this, Submodule.inf_iInf]
  conv_rhs =>
    enter [1]
    ext
    rw [p.inf_genEigenspace (f _) (h _)]

variable [IsDomain R] [IsTorsionFree R M]
/-
**Module.End.disjoint_iInf_maxGenEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.En
d`。
形式化陈述：disjoint_iInf_maxGenEigenspace {χ₁ χ₂ : ι -> R} (h : χ₁ != χ₂) : Disjoint 
(⨅ i, (f i).maxGenEigenspace (χ₁ i)) (⨅ i, (f i).maxGenEigenspace (χ₂ i))
参数：h : χ₁ != χ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
-/
lemma disjoint_iInf_maxGenEigenspace {χ₁ χ₂ : ι → R} (h : χ₁ ≠ χ₂) :
    Disjoint (⨅ i, (f i).maxGenEigenspace (χ₁ i)) (⨅ i, (f i).maxGenEigenspace (χ₂ i)) := by
  obtain ⟨j, hj⟩ : ∃ j, χ₁ j ≠ χ₂ j := Function.ne_iff.mp h
  exact (End.disjoint_genEigenspace (f j) hj ⊤ ⊤).mono (iInf_le _ j) (iInf_le _ j)
/-
**Module.End.injOn_iInf_maxGenEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：injOn_iInf_maxGenEigenspace : InjOn (fun χ : ι -> R => ⨅ i, (f i).maxGenEi
genspace (χ i)) {χ | ⨅ i, (f i).maxGenEigenspace (χ i) != ⊥}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.disjoint_iInf_maxGenEigenspace`：disjoint_iInf_maxGenEigenspac
e {χ₁ χ₂ : ι -> R} (h : χ₁ != χ₂) : Disjoint (⨅ i, (f i).maxGenEigenspace (χ₁ i)
) (⨅ i, (f i).maxGenEigenspace …
-/
lemma injOn_iInf_maxGenEigenspace :
    InjOn (fun χ : ι → R ↦ ⨅ i, (f i).maxGenEigenspace (χ i))
      {χ | ⨅ i, (f i).maxGenEigenspace (χ i) ≠ ⊥} := by
  rintro χ₁ _ χ₂
    hχ₂ (hχ₁₂ : ⨅ i, (f i).maxGenEigenspace (χ₁ i) = ⨅ i, (f i).maxGenEigenspace (χ₂ i))
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_iInf_maxGenEigenspace f hχ₂
/-
**Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo** 是 Mathlib 中的一个
引理，位于命名空间 `Module.End`。
形式化陈述：independent_iInf_maxGenEigenspace_of_forall_mapsTo (h : forall i j φ, Maps
To (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ)) : iSupIndep fun 
χ : ι -> R => ⨅ i, (f i).maxGenEigenspace (χ i)
参数：h : forall i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigens
pace φ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Module.End.mem_iInf_maxGenEigenspace_iff`：mem_iInf_maxGenEigenspace_iff 
(χ : ι -> R) (m : M) : m in ⨅ i, (f i).maxGenEigenspace (χ i) ↔ forall j, exists
 k : Nat, ((f j - χ j • ↑1) ^ …
· 使用定理 `Module.End.coe_pow`：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `Set.MapsTo.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo
 f s s → ∀ (n : ℕ), Set.MapsTo f^[n] s s
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
（共 39 条，此处仅展示前 30 条）
-/
lemma independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (h : ∀ i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ)) :
    iSupIndep fun χ : ι → R ↦ ⨅ i, (f i).maxGenEigenspace (χ i) := by
  replace h (l : ι) (χ : ι → R) :
      MapsTo (f l) (⨅ i, (f i).maxGenEigenspace (χ i)) (⨅ i, (f i).maxGenEigenspace (χ i)) := by
    intro x hx
    simp only [iInf_eq_iInter, mem_iInter, SetLike.mem_coe] at hx ⊢
    exact fun i ↦ h l i (χ i) (hx i)
  classical
  suffices ∀ χ (s : Finset (ι → R)) (_ : χ ∉ s),
      Disjoint (⨅ i, (f i).maxGenEigenspace (χ i))
        (s.sup fun (χ : ι → R) ↦ ⨅ i, (f i).maxGenEigenspace (χ i)) by
    simpa only [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase] using! fun s χ _ ↦ this _ _ (s.notMem_erase χ)
  intro χ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert χ₂ s _n ih =>
  intro hχ₁₂
  obtain ⟨hχ₁₂ : χ₁ ≠ χ₂, hχ₁ : χ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hχ₁₂
  specialize ih hχ₁
  rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x ∈ ⨅ i, (f i).maxGenEigenspace (χ₂ i) by
    rw [← Submodule.mem_bot (R := R), ← (disjoint_iInf_maxGenEigenspace f hχ₁₂).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  suffices ∀ l, ∃ (k : ℕ),
      ((f l - algebraMap R (Module.End R M) (χ₂ l)) ^ k) (y + z) ∈
      (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ⊓
        Finset.sup s fun χ ↦ ⨅ i, (f i).maxGenEigenspace (χ i) by
    simpa [ih.eq_bot, Submodule.mem_bot] using! this
  intro l
  let g : Module.End R M := f l - algebraMap R (Module.End R M) (χ₂ l)
  obtain ⟨k, hk : (g ^ k) y = 0⟩ := (mem_iInf_maxGenEigenspace_iff _ _ _).mp hy l
  have aux (f : End R M) (φ : R) (k : ℕ) (p : Submodule R M) (hp : MapsTo f p p) :
      MapsTo ((f - algebraMap R (Module.End R M) φ) ^ k) p p := by
    rw [Module.End.coe_pow]
    exact MapsTo.iterate (fun m hm ↦ p.sub_mem (hp hm) (p.smul_mem _ hm)) k
  refine ⟨k, Submodule.mem_inf.mp ⟨?_, ?_⟩⟩
  · refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ?_ hx
    simp only [Submodule.coe_iInf]
    exact h l χ₁
  · rw [map_add, hk, zero_add]
    suffices (s.sup fun χ ↦ (⨅ i, (f i).maxGenEigenspace (χ i))).map (g ^ k) ≤
        s.sup fun χ ↦ (⨅ i, (f i).maxGenEigenspace (χ i)) from
      this (Submodule.mem_map_of_mem hz)
    simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := ι → R), Submodule.map_iSup (ι := _ ∈ s)]
    refine iSup₂_mono fun χ _ ↦ ?_
    rintro - ⟨u, hu, rfl⟩
    refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ i)) ?_ hu
    simp only [Submodule.coe_iInf]
    exact h l χ

/-- Given a family of endomorphisms `i ↦ f i` which are compatible in the sense that every maximal
generalised eigenspace of `f i` is invariant w.r.t. `f j`, if each `f i` is triangularizable, the
family is simultaneously triangularizable. -/
/-
**Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo** 是 Mathlib 中的一个
引理，位于命名空间 `Module.End`。
形式化陈述：iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M]
 (f : ι -> End K M) (h : forall i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) (
(f j).maxGenEigenspace φ)) (h' : forall i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) : 
⨆ χ : ι -> K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤
参数：f : ι -> End K M；h : forall i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((
f j).maxGenEigenspace φ)；h' : forall i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `forall_or_exists_not`：forall_or_exists_not (P : α -> Prop) : (forall a, 
P a) ∨ exists a, ¬P a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submodule.finrank_lt`：finrank_lt [FiniteDimensional K V] {s : Submodule 
K V} (h : s != ⊤) : finrank K s < finrank K V
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Module.End.mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo`：mapsTo_r
estrict_maxGenEigenspace_restrict_of_mapsTo {p : Submodule R M} (f g : End R M) 
(hf : MapsTo f p p) (hg : MapsTo g p p) {μ₁ μ₂ : R} …
· 使用定理 `Module.End.genEigenspace_restrict_eq_top`：Module.End.genEigenspace_restr
ict_eq_top {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V] {k :
 Nat∞} (h : forall x in p, f x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`：∀ {ι : Type u_1} {
R : Type u_2} {M : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] (f : ι → Module.…
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Given a family of endomorphisms `i ↦ f i` which are compatible in the sense that
 every maximal
generalised eigenspace of `f i` is invariant w.r.t. `f j`, if each `f i` is tria
ngularizable, the
family is simultaneously triangularizable.
-/
lemma iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M]
    (f : ι → End K M)
    (h : ∀ i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  generalize h_dim : finrank K M = n
  induction n using Nat.strongRecOn generalizing M with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ ∃ φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι ↦ ∃ φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
    replace hχ : ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by simpa
    simp_rw [eq_top_iff] at hχ ⊢
    exact le_trans hχ <| le_iSup (fun χ : ι → K ↦ ⨅ i, (f i).maxGenEigenspace (χ i)) χ
  · replace hy : ∀ φ, finrank K ((f i).maxGenEigenspace φ) < n := fun φ ↦ by
      simp_rw [not_exists, ← lt_top_iff_ne_top] at hy; exact h_dim ▸ Submodule.finrank_lt (hy φ).ne
    have hi (j : ι) (φ : K) :
        MapsTo (f j) ((f i).maxGenEigenspace φ) ((f i).maxGenEigenspace φ) := by
      exact h j i φ
    replace ih (φ : K) :
        ⨆ χ : ι → K, ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      apply ih _ (hy φ)
      · intro j k μ
        exact mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f j) (f k) _ _ (h j k μ)
      · exact fun j ↦ Module.End.genEigenspace_restrict_eq_top _ (h' j)
      · rfl
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      suffices ∀ χ : ι → K, χ i ≠ φ → ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊥ by
        specialize ih φ; rw [iSup_split, biSup_congr this] at ih; simpa using ih
      intro χ hχ
      rw [eq_bot_iff, ← ((f i).maxGenEigenspace φ).ker_subtype, LinearMap.ker,
        ← Submodule.map_le_iff_le_comap, ← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo,
        ← disjoint_iff_inf_le]
      exact ((f i).disjoint_genEigenspace hχ.symm _ _).mono_right (iInf_le _ i)
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace (f j) (χ j) =
        maxGenEigenspace (f i) φ := by
      have (χ : ι → K) (hχ : χ i = φ) : ⨅ j, maxGenEigenspace (f j) (χ j) =
          (⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j)).map
            ((f i).maxGenEigenspace φ).subtype := by
        rw [← hχ, iInf_maxGenEigenspace_restrict_map_subtype_eq]
      simp_rw [biSup_congr this, ← Submodule.map_iSup, ih, Submodule.map_top,
        Submodule.range_subtype]
    simpa only [← ih, iSup_comm (ι := K), iSup_iSup_eq_right] using h' i

/-- A commuting family of triangularizable endomorphisms is simultaneously triangularizable. -/
/-
**Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_o
f_commute** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commu
te [FiniteDimensional K M] (f : ι -> Module.End K M) (h : Pairwise fun i j => Co
mmute (f i) (f j)) (h' : forall i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) : ⨆ χ : ι 
-> K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤
参数：f : ι -> Module.End K M；h : Pairwise fun i j => Commute (f i) (f j)；h' : fora
ll i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`：iSup_iInf
_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M] (f : ι -> End 
K M) (h : forall i j φ, MapsTo (f i) ((f j).maxGenE…
· 使用引理 `Module.End.mapsTo_maxGenEigenspace_of_comm`：mapsTo_maxGenEigenspace_of_c
omm {f g : End R M} (h : Commute f g) (μ : R) : MapsTo g ↑(f.maxGenEigenspace μ)
 ↑(f.maxGenEigenspace μ)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y

--- 原说明 ---
A commuting family of triangularizable endomorphisms is simultaneously triangula
rizable.
-/
theorem iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    [FiniteDimensional K M] (f : ι → Module.End K M) (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j ↦ Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

end Module.End

