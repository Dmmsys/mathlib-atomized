/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Module.Basic

/-!
# Make `fun_prop` work for finite (multiplicative) support

We provide API lemmas for the predicate `HasFiniteMulSupport` (and its additivized version
`HasFiniteSupport`) on functions so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support.
-/

public section

namespace Function

variable {α M : Type*} [One M]

@[to_additive (attr := fun_prop)]
/-
**Function.hasFiniteMulSupport_fun_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：hasFiniteMulSupport_fun_one : HasFiniteMulSupport (1 : α -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_one`：mulSupport_one : mulSupport (1 : ι -> M) = ∅
-/
lemma hasFiniteMulSupport_fun_one : HasFiniteMulSupport (1 : α → M) := by
  simp [HasFiniteMulSupport]

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasF
initeMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {N : Type u_3} [inst_1 : On
e N] {g : M → N} {f : α → M},   Function.HasFiniteMulSupport f → g 1 = 1 → Funct
ion.HasFiniteMulSupport fun a => g (f a)
参数：f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.mulSupport_comp_subset`：mulSupport_comp_subset {g : M -> N} (hg
 : g 1 = 1) (f : ι -> M) : mulSupport (g ∘ f) subseteq mulSupport f
-/
lemma HasFiniteMulSupport.fun_comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a ↦ g (f a) :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {N : Type u_3} [inst_1 : On
e N] {g : M → N} {f : α → M},   Function.HasFiniteMulSupport f → g 1 = 1 → Funct
ion.HasFiniteMulSupport (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.mulSupport_comp_subset`：mulSupport_comp_subset {g : M -> N} (hg
 : g 1 = 1) (f : ι -> M) : mulSupport (g ∘ f) subseteq mulSupport f
-/
lemma HasFiniteMulSupport.comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport (g ∘ f) :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.fst** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {M' : Type u_3} [inst_1 : O
ne M'] {f : α → M × M'},   Function.HasFiniteMulSupport f → Function.HasFiniteMu
lSupport fun a => (f a).1
参数：f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Function.Ha
sFiniteMulSupport f → g…
-/
lemma HasFiniteMulSupport.fst {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).fst :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.snd** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {M' : Type u_3} [inst_1 : O
ne M'] {f : α → M × M'},   Function.HasFiniteMulSupport f → Function.HasFiniteMu
lSupport fun a => (f a).2
参数：f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Function.Ha
sFiniteMulSupport f → g…
-/
lemma HasFiniteMulSupport.snd {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).snd :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFin
iteMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {M' : Type u_3} [inst_1 : O
ne M'] {f : α → M} {g : α → M'},   Function.HasFiniteMulSupport f → Function.Has
FiniteMulSupport g → Function.HasFiniteMulSupport fun a => (f a, g a)
参数：f a, g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_prodMk`：mulSupport_prodMk (f : ι -> M) (g : ι -> N) 
: mulSupport (fun x => (f x, g x)) = mulSupport f union mulSupport g
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
lemma HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Function.HasFiniteMulSupport.mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : MulOneClass M] {f g : α → M},   Fu
nction.HasFiniteMulSupport f → Function.HasFiniteMulSupport g → Function.HasFini
teMulSupport (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Function.mulSupport_mul`：mulSupport_mul [MulOneClass M] (f g : α -> M) :
 (mulSupport fun x => f x * g x) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.mul {M : Type*} [MulOneClass M] {f g : α → M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f * g) :=
  (hf.union hg).subset <| mulSupport_mul ..

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Function.HasFiniteMulSupport.inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : DivisionMonoid M] {f : α → M},   F
unction.HasFiniteMulSupport f → Function.HasFiniteMulSupport f⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Function.Ha
sFiniteMulSupport f → g…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma HasFiniteMulSupport.inv {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport f⁻¹ :=
  hf.comp inv_one

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.prod** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : CommMonoid M] {ι : Type u_4} {f : 
ι → α → M},   (∀ (i : ι), Function.HasFiniteMulSupport (f i)) →     ∀ (s : Finse
t ι), Function.HasFiniteMulSupport fun a => ∏ i ∈ s, f i a
参数：∀ (i : ι), Function.HasFiniteMulSupport (f i)；s : Finset ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `Finset.mulSupport_prod`：mulSupport_prod (s : Finset ι) (f : ι -> κ -> M)
 : mulSupport (fun x => ∏ i in s, f i x) subseteq ⋃ i in s, mulSupport (f i)
-/
lemma HasFiniteMulSupport.prod {M : Type*} [CommMonoid M] {ι : Type*} {f : ι → α → M}
    (hf : ∀ i, HasFiniteMulSupport (f i)) (s : Finset ι) :
    HasFiniteMulSupport fun a ↦ ∏ i ∈ s, f i a :=
  (s.finite_toSet.biUnion fun i _ ↦ hf i).subset <| s.mulSupport_prod f

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Function.HasFiniteMulSupport.div** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : DivisionMonoid M] {f g : α → M},  
 Function.HasFiniteMulSupport f → Function.HasFiniteMulSupport g → Function.HasF
initeMulSupport (f / g)
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Function.mulSupport_div`：mulSupport_div : (mulSupport fun x => f x / g x
) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.div {M : Type*} [DivisionMonoid M] {f g : α → M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f / g) :=
  (hf.union hg).subset <| mulSupport_div ..

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Function.HasFiniteMulSupport.pow** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : Monoid M] {f : α → M},   Function.
HasFiniteMulSupport f → ∀ (n : ℕ), Function.HasFiniteMulSupport (f ^ n)
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Function.Ha
sFiniteMulSupport f → g…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma HasFiniteMulSupport.pow {M : Type*} [Monoid M] {f : α → M} (hf : HasFiniteMulSupport f)
    (n : ℕ) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_pow n)

@[to_additive (attr := to_fun (attr := fun_prop))]
/-
**Function.HasFiniteMulSupport.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_3} [inst : DivisionMonoid M] {f : α → M},   F
unction.HasFiniteMulSupport f → ∀ (n : ℤ), Function.HasFiniteMulSupport (f ^ n)
参数：n : ℤ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Function.Ha
sFiniteMulSupport f → g…
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
-/
lemma HasFiniteMulSupport.zpow {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) (n : ℤ) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_zpow n)

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.max** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : LinearOrder M] {f
 g : α → M},   Function.HasFiniteMulSupport f →     Function.HasFiniteMulSupport
 g → Function.HasFiniteMulSupport fun a => max (f a) (g a)
参数：f a；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用引理 `Function.mulSupport_max`：mulSupport_max [LinearOrder M] (f g : α -> M) :
 mulSupport (fun x => max (f x) (g x)) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.max [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ max (f a) (g a) :=
  (hf.union hg).subset <| mulSupport_max ..

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.min** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : LinearOrder M] {f
 g : α → M},   Function.HasFiniteMulSupport f →     Function.HasFiniteMulSupport
 g → Function.HasFiniteMulSupport fun a => min (f a) (g a)
参数：f a；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用引理 `Function.mulSupport_min`：mulSupport_min [LinearOrder M] (f g : α -> M) :
 mulSupport (fun x => min (f x) (g x)) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.min [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ min (f a) (g a) :=
  (hf.union hg).subset <| mulSupport_min ..

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.sup** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : SemilatticeSup M]
 {f g : α → M},   Function.HasFiniteMulSupport f → Function.HasFiniteMulSupport 
g → Function.HasFiniteMulSupport fun a => f a ⊔ g a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用引理 `Function.mulSupport_sup`：mulSupport_sup [SemilatticeSup M] (f g : α -> M
) : mulSupport (fun x => f x ⊔ g x) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.sup [SemilatticeSup M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊔ g a :=
  (hf.union hg).subset <| mulSupport_sup ..

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.inf** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinite
MulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : SemilatticeInf M]
 {f g : α → M},   Function.HasFiniteMulSupport f → Function.HasFiniteMulSupport 
g → Function.HasFiniteMulSupport fun a => f a ⊓ g a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用引理 `Function.mulSupport_inf`：mulSupport_inf [SemilatticeInf M] (f g : α -> M
) : mulSupport (fun x => f x ⊓ g x) subseteq mulSupport f union mulSupport g
-/
lemma HasFiniteMulSupport.inf [SemilatticeInf M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊓ g a :=
  (hf.union hg).subset <| mulSupport_inf ..

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : ConditionallyComp
leteLattice M] {ι : Sort u_3} [Nonempty ι]   [Finite ι] {f : ι → α → M},   (∀ (i
 : ι), Function.HasFiniteMulSupport (f i)) → Function.HasFiniteMulSupport fun a 
=> ⨆ i, f i a
参数：∀ (i : ι), Function.HasFiniteMulSupport (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用引理 `Function.mulSupport_iSup`：mulSupport_iSup [ConditionallyCompleteLattice 
M] [Nonempty ι] (f : ι -> α -> M) : mulSupport (fun x => ⨆ i, f i x) subseteq ⋃ 
i, mulSupport …
-/
lemma HasFiniteMulSupport.iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨆ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iSup f

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : ConditionallyComp
leteLattice M] {ι : Sort u_3} [Nonempty ι]   [Finite ι] {f : ι → α → M},   (∀ (i
 : ι), Function.HasFiniteMulSupport (f i)) → Function.HasFiniteMulSupport fun a 
=> ⨅ i, f i a
参数：∀ (i : ι), Function.HasFiniteMulSupport (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用引理 `Function.mulSupport_iInf`：mulSupport_iInf [ConditionallyCompleteLattice 
M] [Nonempty ι] (f : ι -> α -> M) : mulSupport (fun x => ⨅ i, f i x) subseteq ⋃ 
i, mulSupport …
-/
lemma HasFiniteMulSupport.iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨅ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iInf f

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.pi** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFiniteM
ulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {ι : Type u_3} [Finite α] {
f : ι → α → M},   (∀ (a : α), Function.HasFiniteMulSupport fun x => f x a) → Fun
ction.HasFiniteMulSupport f
参数：∀ (a : α), Function.HasFiniteMulSupport fun x => f x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
-/
lemma HasFiniteMulSupport.pi {ι : Type*} [Finite α] {f : ι → α → M}
    (hf : ∀ a, HasFiniteMulSupport (f · a)) :
    HasFiniteMulSupport f := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi ↦ ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.sup'** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : SemilatticeSup M]
 {ι : Type u_3} {f : ι → α → M}   (s : Finset ι),   (∀ i ∈ s, Function.HasFinite
MulSupport (f i)) →     ∀ (hs : s.Nonempty), Function.HasFiniteMulSupport fun a 
=> s.sup' hs fun x => f x a
参数：s : Finset ι；∀ i ∈ s, Function.HasFiniteMulSupport (f i)；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.sup'_eq_of_forall`：∀ {α : Type u_2} {β : Type u_3} [inst : Semila
tticeSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b
 = a) → s.sup'…
-/
lemma HasFiniteMulSupport.sup' [SemilatticeSup M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.sup' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x ↦ f x a) ha

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.inf'** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFinit
eMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] [inst_1 : SemilatticeInf M]
 {ι : Type u_3} {f : ι → α → M}   (s : Finset ι),   (∀ i ∈ s, Function.HasFinite
MulSupport (f i)) →     ∀ (hs : s.Nonempty), Function.HasFiniteMulSupport fun a 
=> s.inf' hs fun x => f x a
参数：s : Finset ι；∀ i ∈ s, Function.HasFiniteMulSupport (f i)；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.inf'_eq_of_forall`：∀ {α : Type u_2} {β : Type u_3} [inst : Semila
tticeInf α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b
 = a) → s.inf'…
-/
lemma HasFiniteMulSupport.inf' [SemilatticeInf M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.inf' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x ↦ f x a) ha

variable {β : Type*} {f : β → M} {g : α → β}

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.comp_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.HasFiniteMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {β : Type u_3} {f : β → M} 
{g : α → β},   Function.Injective g → Function.HasFiniteMulSupport f → Function.
HasFiniteMulSupport (f ∘ g)
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_injOn`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α}
 {t : Set β}, Set.MapsTo f s t → Set.InjOn f s → t.Finite → s.Finite
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
lemma HasFiniteMulSupport.comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage, Function.mulSupport]

@[to_additive (attr := fun_prop)]
/-
**Function.HasFiniteMulSupport.fun_comp_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `
Function.HasFiniteMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {β : Type u_3} {f : β → M} 
{g : α → β},   Function.Injective g → Function.HasFiniteMulSupport f → Function.
HasFiniteMulSupport fun a => f (g a)
参数：g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.comp_of_injective`：∀ {α : Type u_1} {M : Ty
pe u_2} [inst : One M] {β : Type u_3} {f : β → M} {g : α → β},   Function.Inject
ive g → Function.HasFiniteMulSupport…
-/
lemma HasFiniteMulSupport.fun_comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (fun a ↦ f (g a)).HasFiniteMulSupport :=
  hf.comp_of_injective hg

@[to_additive]
/-
**Function.HasFiniteMulSupport.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFi
niteMulSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : One M] {β : Type u_3} {f : β → M} 
{g : α → β} [inst_1 : One β],   Function.HasFiniteMulSupport (f ∘ g) → f 1 = 1 →
 Function.Injective f → Function.HasFiniteMulSupport g
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Injective f) :
    g.HasFiniteMulSupport := by
  refine Set.Finite.subset hfg fun _ ha ↦ Set.mem_ofPred.mpr fun H ↦ Set.mem_ofPred.mp ha ?_
  grind

-- The additive version is a special case of `Function.HasFiniteSupport.smul_left`.
@[fun_prop]
/-
**Function.HasFiniteSupport.hasFiniteMulSupport_fun_pow** 是 Mathlib 中的一个定理，位于命名空
间 `Function.HasFiniteSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : Monoid M] (f : α → M) {g : α → ℕ},
   Function.HasFiniteSupport g → Function.HasFiniteMulSupport fun a => f a ^ g a
参数：f : α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma HasFiniteSupport.hasFiniteMulSupport_fun_pow {M : Type*} [Monoid M] (f : α → M) {g : α → ℕ}
    (hg : g.HasFiniteSupport) :
    (fun a : α ↦ f a ^ g a).HasFiniteMulSupport :=
  Set.Finite.subset hg fun a ha ↦ by contrapose! ha; simp_all

section MulZeroClass

variable {M : Type*} [MulZeroClass M]

@[to_fun (attr := fun_prop)]
/-
**Function.HasFiniteSupport.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFini
teSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : MulZeroClass M] {f : α → M},   Fun
ction.HasFiniteSupport f → ∀ (g : α → M), Function.HasFiniteSupport (f * g)
参数：g : α → M；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.support_mul_subset_left`：support_mul_subset_left (f g : ι -> M₀
) : support (fun x => f x * g x) subseteq support f
-/
lemma HasFiniteSupport.mul_left {f : α → M} (hf : f.HasFiniteSupport) (g : α → M) :
    (f * g).HasFiniteSupport :=
  Set.Finite.subset hf fun _ ha ↦ support_mul_subset_left f g ha

@[to_fun (attr := fun_prop)]
/-
**Function.HasFiniteSupport.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasFin
iteSupport`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : MulZeroClass M] (f : α → M) {g : α
 → M},   Function.HasFiniteSupport g → Function.HasFiniteSupport (f * g)
参数：f : α → M；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.support_mul_subset_right`：support_mul_subset_right (f g : ι -> 
M₀) : support (fun x => f x * g x) subseteq support g
-/
lemma HasFiniteSupport.mul_right (f : α → M) {g : α → M} (hg : g.HasFiniteSupport) :
    (f * g).HasFiniteSupport :=
  Set.Finite.subset hg fun _ ha ↦ support_mul_subset_right f g ha

end MulZeroClass

end Function

@[fun_prop]
/-
**Multiset.hasFiniteSupport_count** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.hasFiniteSupport_count {α : Type*} [DecidableEq α] (s : Multiset 
α) : (count · s).HasFiniteSupport
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Multiset.hasFiniteSupport_count {α : Type*} [DecidableEq α] (s : Multiset α) :
    (count · s).HasFiniteSupport :=
  s.toFinset.finite_toSet.subset <| by simp

end

namespace Function.HasFiniteSupport

public section SMul

variable {α R M : Type*} [Zero M]

@[to_fun (attr := fun_prop)]
/-
**Function.HasFiniteSupport.smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Function.HasFin
iteSupport`。
形式化陈述：smul_left [Zero R] [SMulWithZero R M] {f : α -> R} (hf : f.HasFiniteSuppor
t) (g : α -> M) : (f • g).HasFiniteSupport
参数：hf : f.HasFiniteSupport；g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f
-/
lemma smul_left [Zero R] [SMulWithZero R M] {f : α → R} (hf : f.HasFiniteSupport) (g : α → M) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hf fun _ ha ↦ support_smul_subset_left f g ha

@[to_fun (attr := fun_prop)]
/-
**Function.HasFiniteSupport.smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Function.HasFi
niteSupport`。
形式化陈述：smul_right [SMulZeroClass R M] (f : α -> R) {g : α -> M} (hg : g.HasFinite
Support) : (f • g).HasFiniteSupport
参数：f : α -> R；hg : g.HasFiniteSupport。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Function.support_smul_subset_right`：support_smul_subset_right [Zero M] [
SMulZeroClass R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq support 
g
-/
lemma smul_right [SMulZeroClass R M] (f : α → R) {g : α → M} (hg : g.HasFiniteSupport) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hg fun _ ha ↦ support_smul_subset_right f g ha

end SMul

end Function.HasFiniteSupport

