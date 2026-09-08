/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Matroid Closure

A flat (`IsFlat`) of a matroid `M` is a combinatorial analogue of a subspace of a vector space,
and is defined to be a subset `F` of the ground set of `M` such that for each basis
`I` for `F`, every set having `I` as a basis is contained in `F`.

The *closure* of a set `X` in a matroid `M` is the intersection of all flats of `M` containing `X`.
This is a combinatorial analogue of the linear span of a set of vectors.

For `M : Matroid α`, this file defines a predicate `M.IsFlat : Set α → Prop` and a function
`M.closure : Set α → Set α` corresponding to these notions, and develops API for the latter.
API for `Matroid.IsFlat` will appear in another file; we include the definition here since
it is used in the definition of `Matroid.closure`.

We also define a predicate `Spanning`, to describe a set whose closure is the entire ground set.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.IsFlat F` means that `F` is an isFlat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.closure X` is the closure of `X` in `M`.
* For `M : Matroid α` and `X : ↑(Iic M.E)` (i.e. a bundled subset of `M.E`),
  `M.subtypeClosure X` is the closure of `X`, viewed as a term in `↑(Iic M.E)`.
  This is a `ClosureOperator` on `↑(Iic M.E)`.
* For `M : Matroid α` and `S ⊆ M.E`, `M.Spanning S` means that `S` has closure equal to `M.E`,
  or equivalently that `S` contains an isBase of `M`.

## Implementation details

If `X : Set α` satisfies `X ⊆ M.E`, then it is clear how `M.closure X` should be defined.
But `M.closure X` also needs to be defined for all `X : Set α`,
so a convention is needed for how it handles sets containing junk elements outside `M.E`.
All such choices come with tradeoffs. Provided that `M.closure X` has already been defined
for `X ⊆ M.E`, the two best candidates for extending it to all `X` seem to be:

(1) The function for which `M.closure X = M.closure (X ∩ M.E)` for all `X : Set α`

(2) The function for which `M.closure X = M.closure (X ∩ M.E) ∪ X` for all `X : Set α`

For both options, the function `closure` is monotone and idempotent with no assumptions on `X`.

Choice (1) has the advantage that `M.closure X ⊆ M.E` holds for all `X` without the assumption
that `X ⊆ M.E`, which is very nice for `aesop_mat`. It is also fairly convenient to rewrite
`M.closure X` to `M.closure (X ∩ M.E)` when one needs to work with a subset of the ground set.
Its disadvantage is that the statement `X ⊆ M.closure X` is only true provided that `X ⊆ M.E`.

Choice (2) has the reverse property: we would have `X ⊆ M.closure X` for all `X`,
but the condition `M.closure X ⊆ M.E` requires `X ⊆ M.E` to hold.
It has a couple of other advantages too: it is actually the closure function of a matroid on `α`
with ground set `univ` (specifically, the direct sum of `M` and a free matroid on `M.Eᶜ`),
and because of this, it is an example of a `ClosureOperator` on `α`, which in turn gives access
to nice existing API for both `ClosureOperator` and `GaloisInsertion`.
This also relates to flats; `F ⊆ M.E ∧ ClosureOperator.IsClosed F` is equivalent to `M.IsFlat F`.
(All of this fails for choice (1), since `X ⊆ M.closure X` is required for
a `ClosureOperator`, but isn't true for non-subsets of `M.E`)

The API that choice (2) would offer is very beguiling, but after extensive experimentation in
an external repo, it seems that (1) is far less rough around the edges in practice,
so we go with (1). It may be helpful at some point to define a primed version
`Matroid.closure' : ClosureOperator (Set α)` corresponding to choice (2).
Failing that, the `ClosureOperator`/`GaloisInsertion` API is still available on
the subtype `↑(Iic M.E)` via `Matroid.SubtypeClosure`, albeit less elegantly.

## Naming conventions

In lemma names, the words `spanning` and `isFlat` are used as suffixes,
for instance we have `ground_spanning` rather than `spanning_ground`.
-/

@[expose] public section

assert_not_exists Field

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y : Set α} {e f : α}

section IsFlat

/-- A flat is a maximal set having a given basis -/
@[mk_iff]
/-
**Matroid.IsFlat** 是 Mathlib 中的一个结构，位于命名空间 `Matroid`。
形式化陈述：IsFlat (M : Matroid α) (F : Set α) : Prop where subset_of_isBasis_of_isBas
is : forall ⦃I X⦄, M.IsBasis I F -> M.IsBasis I X -> X subseteq F subset_ground 
: F subseteq M.E  attribute [aesop unsafe 20% (rule_sets
参数：M : Matroid α；F : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A flat is a maximal set having a given basis
-/
structure IsFlat (M : Matroid α) (F : Set α) : Prop where
  subset_of_isBasis_of_isBasis : ∀ ⦃I X⦄, M.IsBasis I F → M.IsBasis I X → X ⊆ F
  subset_ground : F ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsFlat.subset_ground
/-
**Matroid.ground_isFlat** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α), M.IsFlat M.E
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
@[simp] lemma ground_isFlat (M : Matroid α) : M.IsFlat M.E :=
  ⟨fun _ _ _ ↦ IsBasis.subset_ground, Subset.rfl⟩
/-
**Matroid.IsFlat.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsFlat`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {ι : Type u_3} [Nonempty ι] {Fs : ι → Set
 α},   (∀ (i : ι), M.IsFlat (Fs i)) → M.IsFlat (⋂ i, Fs i)
参数：∀ (i : ι), M.IsFlat (Fs i)；⋂ i, Fs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `Matroid.IsFlat.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {F : Set 
α}, M.IsFlat F → F ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Matroid.IsFlat.subset_of_isBasis_of_isBasis`：∀ {α : Type u_2} {M : Matro
id α} {F : Set α}, M.IsFlat F → ∀ ⦃I X : Set α⦄, M.IsBasis I F → M.IsBasis I X →
 X ⊆ F
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Matroid.IsBasis.isBasis_union`：∀ {α : Type u_1} {M : Matroid α} {I X Y :
 Set α}, M.IsBasis I X → M.IsBasis I Y → M.IsBasis I (X ∪ Y)
· 使用定理 `Matroid.IsBasis.isBasis_union_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → M.IsBasis J (J ∪ X)
-/
lemma IsFlat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.IsFlat (Fs i)) : M.IsFlat (⋂ i, Fs i) := by
  refine ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine subset_union_right.trans ((hFs i).1 (X := Fs i ∪ X) hIJ ?_)
  convert! hIJ.isBasis_union (hIX.isBasis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

/-- The property of being a flat gives rise to a `ClosureOperator` on the subsets of `M.E`,
in which the `IsClosed` sets correspond to flats.
(We can't define such an operator on all of `Set α`,
since this would incorrectly force `univ` to always be a flat.) -/
/-
**Matroid.subtypeClosure** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E)
参数：M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of being a flat gives rise to a `ClosureOperator` on the subsets of
 `M.E`,
in which the `IsClosed` sets correspond to flats.
(We can't define such an operator on all of `Set α`,
since this would incorrectly force `univ` to always be a flat.)
-/
def subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E) :=
  ClosureOperator.ofCompletePred (fun F ↦ M.IsFlat F.1) fun s hs ↦ by
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · simp
    have _ := hne.coe_sort
    convert! IsFlat.iInter (M := M) (Fs := fun (F : s) ↦ F.1.1) (fun F ↦ hs F.1 F.2)
    ext
    aesop
/-
**Matroid.isFlat_iff_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isFlat_iff_isClosed : M.IsFlat F ↔ exists h : F subseteq M.E, M.subtypeClo
sure.IsClosed ⟨F, h⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ClosureOperator.ofCompletePred_isClosed`：∀ {α : Type u_1} [inst : Comple
teLattice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s))
 (a : α),   (ClosureOperator.…
· 使用定理 `Matroid.IsFlat.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {F : Set 
α}, M.IsFlat F → F ⊆ M.E
-/
lemma isFlat_iff_isClosed : M.IsFlat F ↔ ∃ h : F ⊆ M.E, M.subtypeClosure.IsClosed ⟨F, h⟩ := by
  simpa [subtypeClosure] using IsFlat.subset_ground
/-
**Matroid.isClosed_iff_isFlat** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isClosed_iff_isFlat {F : Iic M.E} : M.subtypeClosure.IsClosed F ↔ M.IsFlat
 F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.ofCompletePred_isClosed`：∀ {α : Type u_1} [inst : Comple
teLattice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s))
 (a : α),   (ClosureOperator.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isClosed_iff_isFlat {F : Iic M.E} : M.subtypeClosure.IsClosed F ↔ M.IsFlat F := by
  simp [subtypeClosure]

end IsFlat

/-- The closure of `X ⊆ M.E` is the intersection of all the flats of `M` containing `X`.
A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.closure X := M.closure (X ∩ M.E)`. -/
/-
**Matroid.closure** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：closure (M : Matroid α) (X : Set α) : Set α
参数：M : Matroid α；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of `X ⊆ M.E` is the intersection of all the flats of `M` containing 
`X`.
A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.closure X := M.cl
osure (X ∩ M.E)`.
-/
def closure (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F}
/-
**Matroid.closure_def** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_def (M : Matroid α) (X : Set α) : M.closure X = ⋂₀ {F | M.IsFlat F
 ∧ X inter M.E subseteq F}
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma closure_def (M : Matroid α) (X : Set α) : M.closure X = ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F} :=
  rfl
/-
**Matroid.closure_def'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_def' (M : Matroid α) (X : Set α) (hX : X subseteq M.E
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.closure.eq_1`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.cl
osure X = ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F}
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
lemma closure_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {F | M.IsFlat F ∧ X ⊆ F} := by
  rw [closure, inter_eq_self_of_subset_left hX]
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty {F | M.IsFlat F ∧ X ∩ M.E ⊆ F} := ⟨M.E, M.ground_isFlat, inter_subset_right⟩
/-
**Matroid.closure_eq_subtypeClosure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_eq_subtypeClosure (M : Matroid α) (X : Set α) : M.closure X = M.su
btypeClosure ⟨X inter M.E, inter_subset_right⟩
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ground_isFlat`：∀ {α : Type u_2} (M : Matroid α), M.IsFlat M.E
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Matroid.IsFlat.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {F : Set 
α}, M.IsFlat F → F ⊆ M.E
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用定理 `Set.Iic.coe_iInf`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattic
e α] {a : α} (f : ι → ↑(Set.Iic a)), ↑(⨅ i, f i) = a ⊓ ⨅ i, ↑(f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
lemma closure_eq_subtypeClosure (M : Matroid α) (X : Set α) :
    M.closure X = M.subtypeClosure ⟨X ∩ M.E, inter_subset_right⟩  := by
  suffices ∀ (x : α), (∀ (t : Set α), M.IsFlat t → X ∩ M.E ⊆ t → x ∈ t) ↔
    (x ∈ M.E ∧ ∀ a ⊆ M.E, X ∩ M.E ⊆ a → M.IsFlat a → x ∈ a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨h _ M.ground_isFlat inter_subset_right, fun F _ hXF hF ↦ h F hF hXF⟩,
    fun ⟨_, h⟩ F hF hXF ↦ h F hF.subset_ground hXF hF⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.closure_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_subset_ground (M : Matroid α) (X : Set α) : M.closure X subseteq M
.E
参数：M : Matroid α；X : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Matroid.ground_isFlat`：∀ {α : Type u_2} (M : Matroid α), M.IsFlat M.E
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma closure_subset_ground (M : Matroid α) (X : Set α) : M.closure X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_isFlat, inter_subset_right⟩
/-
**Matroid.ground_subset_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α}, M.E ⊆ M.closure X ↔ M.closur
e X = M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ground_subset_closure_iff : M.E ⊆ M.closure X ↔ M.closure X = M.E := by
  simp [M.closure_subset_ground X, subset_antisymm_iff]
/-
**Matroid.closure_inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.closure (X ∩ M.E) = M.clos
ure X
参数：M : Matroid α；X : Set α；X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma closure_inter_ground (M : Matroid α) (X : Set α) :
    M.closure (X ∩ M.E) = M.closure X := by
  simp_rw [closure_def, inter_assoc, inter_self]
/-
**Matroid.inter_ground_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：inter_ground_subset_closure (M : Matroid α) (X : Set α) : X inter M.E subs
eteq M.closure X
参数：M : Matroid α；X : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma inter_ground_subset_closure (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.closure X := by
  simp_rw [closure_def, subset_sInter_iff]; simp
/-
**Matroid.mem_closure_iff_forall_mem_isFlat** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_iff_forall_mem_isFlat (X : Set α) (hX : X subseteq M.E
参数：X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.closure_def'`：closure_def' (M : Matroid α) (X : Set α) (hX : X s
ubseteq M.E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_closure_iff_forall_mem_isFlat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ ∀ F, M.IsFlat F → X ⊆ F → e ∈ F := by
  simp_rw [M.closure_def' X, mem_sInter, mem_ofPred, and_imp]
/-
**Matroid.subset_closure_iff_forall_subset_isFlat** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：subset_closure_iff_forall_subset_isFlat (X : Set α) (hX : X subseteq M.E
参数：X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.closure_def'`：closure_def' (M : Matroid α) (X : Set α) (hX : X s
ubseteq M.E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subset_closure_iff_forall_subset_isFlat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure X ↔ ∀ F, M.IsFlat F → X ⊆ F → Y ⊆ F := by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_ofPred, and_imp]
/-
**Matroid.subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：subset_closure (M : Matroid α) (X : Set α) (hX : X subseteq M.E
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.closure_def'`：closure_def' (M : Matroid α) (X : Set α) (hX : X s
ubseteq M.E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma subset_closure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure X := by
  simp [M.closure_def' X, subset_sInter_iff]
/-
**Matroid.IsFlat.closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsFlat`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {F : Set α}, M.IsFlat F → M.closure F = F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsFlat.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {F : Set 
α}, M.IsFlat F → F ⊆ M.E
-/
lemma IsFlat.closure (hF : M.IsFlat F) : M.closure F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

variable (X) in
/-
**Matroid.isFlat_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} (X : Set α), M.IsFlat (M.closure X)
参数：X : Set α；M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.closure.eq_1`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.cl
osure X = ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F}
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
· 使用定理 `Matroid.IsFlat.iInter`：∀ {α : Type u_2} {M : Matroid α} {ι : Type u_3} [
Nonempty ι] {Fs : ι → Set α},   (∀ (i : ι), M.IsFlat (Fs i)) → M.IsFlat (⋂ i, Fs
 i)
· 使用定理 `Matroid.instNonemptyElemSetOfPredAndIsFlatLeInterE`：∀ {α : Type u_2} {M 
: Matroid α} {X : Set α}, Nonempty ↑{F | M.IsFlat F ∧ X ∩ M.E ⊆ F}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] lemma isFlat_closure : M.IsFlat (M.closure X) := by
  rw [closure, sInter_eq_iInter]; exact .iInter (·.2.1)
/-
**Matroid.isFlat_iff_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isFlat_iff_closure_eq : M.IsFlat F ↔ M.closure F = F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsFlat.closure`：∀ {α : Type u_2} {M : Matroid α} {F : Set α}, M.
IsFlat F → M.closure F = F
· 使用定理 `Matroid.isFlat_closure`：∀ {α : Type u_2} {M : Matroid α} (X : Set α), M.
IsFlat (M.closure X)
-/
lemma isFlat_iff_closure_eq : M.IsFlat F ↔ M.closure F = F := ⟨(·.closure), (· ▸ isFlat_closure F)⟩
/-
**Matroid.closure_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α), M.closure M.E = M.E
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma closure_ground (M : Matroid α) : M.closure M.E = M.E :=
  (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)
/-
**Matroid.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α), M.closure Set.univ = M.E
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Matroid.closure_ground`：∀ {α : Type u_2} (M : Matroid α), M.closure M.E 
= M.E
-/
@[simp] lemma closure_univ (M : Matroid α) : M.closure univ = M.E := by
  rw [← closure_inter_ground, univ_inter, closure_ground]

@[gcongr]
/-
**Matroid.closure_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_subset_closure (M : Matroid α) (h : X subseteq Y) : M.closure X su
bseteq M.closure Y
参数：M : Matroid α；h : X subseteq Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma closure_subset_closure (M : Matroid α) (h : X ⊆ Y) : M.closure X ⊆ M.closure Y :=
  subset_sInter (fun _ h' ↦ sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)
/-
**Matroid.closure_mono** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_mono (M : Matroid α) : Monotone M.closure
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
-/
lemma closure_mono (M : Matroid α) : Monotone M.closure :=
  fun _ _ ↦ M.closure_subset_closure
/-
**Matroid.closure_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.closure (M.closure X) = M.
closure X
参数：M : Matroid α；X : Set α；M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Matroid.IsFlat.closure`：∀ {α : Type u_2} {M : Matroid α} {F : Set α}, M.
IsFlat F → M.closure F = F
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
@[simp] lemma closure_closure (M : Matroid α) (X : Set α) : M.closure (M.closure X) = M.closure X :=
  (M.subset_closure _).antisymm' (subset_sInter
    (fun F hF ↦ (closure_subset_closure _ (sInter_subset_of_mem hF)).trans hF.1.closure.subset))
/-
**Matroid.closure_subset_closure_of_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Ma
troid`。
形式化陈述：closure_subset_closure_of_subset_closure (hXY : X subseteq M.closure Y) : 
M.closure X subseteq M.closure Y
参数：hXY : X subseteq M.closure Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma closure_subset_closure_of_subset_closure (hXY : X ⊆ M.closure Y) :
    M.closure X ⊆ M.closure Y :=
  (M.closure_subset_closure hXY).trans_eq (M.closure_closure Y)
/-
**Matroid.closure_subset_closure_iff_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `M
atroid`。
形式化陈述：closure_subset_closure_iff_subset_closure (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
-/
lemma closure_subset_closure_iff_subset_closure (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X ⊆ M.closure Y ↔ X ⊆ M.closure Y :=
  ⟨(M.subset_closure X).trans, closure_subset_closure_of_subset_closure⟩
/-
**Matroid.subset_closure_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：subset_closure_of_subset (M : Matroid α) (hXY : X subseteq Y) (hY : Y subs
eteq M.E
参数：M : Matroid α；hXY : X subseteq Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
-/
lemma subset_closure_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure Y :=
  hXY.trans (M.subset_closure Y)
/-
**Matroid.subset_closure_of_subset'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：subset_closure_of_subset' (M : Matroid α) (hXY : X subseteq Y) (hX : X sub
seteq M.E
参数：M : Matroid α；hXY : X subseteq Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用引理 `Matroid.subset_closure_of_subset`：subset_closure_of_subset (M : Matroid 
α) (hXY : X subseteq Y) (hY : Y subseteq M.E
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma subset_closure_of_subset' (M : Matroid α) (hXY : X ⊆ Y) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure Y := by
  rw [← closure_inter_ground]; exact M.subset_closure_of_subset (subset_inter hXY hX)
/-
**Matroid.exists_of_closure_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：exists_of_closure_ssubset (hXY : M.closure X ⊂ M.closure Y) : exists e in 
Y, e ∉ M.closure X
参数：hXY : M.closure X ⊂ M.closure Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : P
reorder α] {a b : α}, a ⊂ b → ¬b ⊆ a
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma exists_of_closure_ssubset (hXY : M.closure X ⊂ M.closure Y) : ∃ e ∈ Y, e ∉ M.closure X := by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)
/-
**Matroid.mem_closure_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_of_mem (M : Matroid α) (h : e in X) (hX : X subseteq M.E
参数：M : Matroid α；h : e in X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
-/
lemma mem_closure_of_mem (M : Matroid α) (h : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X :=
  (M.subset_closure X) h
/-
**Matroid.mem_closure_of_mem'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_of_mem' (M : Matroid α) (heX : e in X) (h : e in M.E
参数：M : Matroid α；heX : e in X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用引理 `Matroid.mem_closure_of_mem`：mem_closure_of_mem (M : Matroid α) (h : e in
 X) (hX : X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma mem_closure_of_mem' (M : Matroid α) (heX : e ∈ X) (h : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X := by
  rw [← closure_inter_ground]
  exact M.mem_closure_of_mem ⟨heX, h⟩
/-
**Matroid.notMem_of_mem_sdiff_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：notMem_of_mem_sdiff_closure (he : e in M.E \ M.closure X) : e ∉ X
参数：he : e in M.E \ M.closure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma notMem_of_mem_sdiff_closure (he : e ∈ M.E \ M.closure X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_closure_of_mem' heX he.1

@[deprecated (since := "2026-06-03")]
alias notMem_of_mem_diff_closure := notMem_of_mem_sdiff_closure

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.mem_ground_of_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_ground_of_mem_closure (he : e in M.closure X) : e in M.E
参数：he : e in M.closure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
-/
lemma mem_ground_of_mem_closure (he : e ∈ M.closure X) : e ∈ M.E :=
  (M.closure_subset_ground _) he
/-
**Matroid.closure_iUnion_closure_eq_closure_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Ma
troid`。
形式化陈述：closure_iUnion_closure_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α)
 : M.closure (⋃ i, M.closure (Xs i)) = M.closure (⋃ i, Xs i)
参数：M : Matroid α；Xs : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Matroid.closure_eq_subtypeClosure`：closure_eq_subtypeClosure (M : Matroi
d α) (X : Set α) : M.closure X = M.subtypeClosure ⟨X inter M.E, inter_subset_rig
ht⟩
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用定理 `Set.Iic.coe_iInf`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattic
e α] {a : α} (f : ι → ↑(Set.Iic a)), ↑(⨅ i, f i) = a ⊓ ⨅ i, ↑(f i)
· 使用定理 `Set.Iic.coe_iSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattic
e α] {a : α} (f : ι → ↑(Set.Iic a)), ↑(⨆ i, f i) = ⨆ i, ↑(f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ClosureOperator.closure_iSup_closure`：closure_iSup_closure (f : ι -> α) 
: c (⨆ i, c (f i)) = c (⨆ i, f i)
-/
lemma closure_iUnion_closure_eq_closure_iUnion (M : Matroid α) (Xs : ι → Set α) :
    M.closure (⋃ i, M.closure (Xs i)) = M.closure (⋃ i, Xs i) := by
  simp_rw [closure_eq_subtypeClosure, iUnion_inter, Subtype.coe_inj]
  convert! M.subtypeClosure.closure_iSup_closure (fun i ↦ ⟨Xs i ∩ M.E, inter_subset_right⟩) <;>
  simp [← iUnion_inter, subtypeClosure]
/-
**Matroid.closure_iUnion_congr** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_iUnion_congr (Xs Ys : ι -> Set α) (h : forall i, M.closure (Xs i) 
= M.closure (Ys i)) : M.closure (⋃ i, Xs i) = M.closure (⋃ i, Ys i)
参数：Xs Ys : ι -> Set α；h : forall i, M.closure (Xs i) = M.closure (Ys i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_iUnion_closure_eq_closure_iUnion`：closure_iUnion_closure
_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α) : M.closure (⋃ i, M.closure
 (Xs i)) = M.closure (⋃ i, Xs i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma closure_iUnion_congr (Xs Ys : ι → Set α) (h : ∀ i, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i, Xs i) = M.closure (⋃ i, Ys i) := by
  simp [h, ← M.closure_iUnion_closure_eq_closure_iUnion]
/-
**Matroid.closure_biUnion_closure_eq_closure_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `M
atroid`。
形式化陈述：closure_biUnion_closure_eq_closure_sUnion (M : Matroid α) (Xs : Set (Set α
)) : M.closure (⋃ X in Xs, M.closure X) = M.closure (⋃₀ Xs)
参数：M : Matroid α；Xs : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用引理 `Matroid.closure_iUnion_closure_eq_closure_iUnion`：closure_iUnion_closure
_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α) : M.closure (⋃ i, M.closure
 (Xs i)) = M.closure (⋃ i, Xs i)
-/
lemma closure_biUnion_closure_eq_closure_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.closure (⋃ X ∈ Xs, M.closure X) = M.closure (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion, biUnion_eq_iUnion, closure_iUnion_closure_eq_closure_iUnion]
/-
**Matroid.closure_biUnion_closure_eq_closure_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `
Matroid`。
形式化陈述：closure_biUnion_closure_eq_closure_biUnion (M : Matroid α) (Xs : ι -> Set 
α) (A : Set ι) : M.closure (⋃ i in A, M.closure (Xs i)) = M.closure (⋃ i in A, X
s i)
参数：M : Matroid α；Xs : ι -> Set α；A : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用引理 `Matroid.closure_iUnion_closure_eq_closure_iUnion`：closure_iUnion_closure
_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α) : M.closure (⋃ i, M.closure
 (Xs i)) = M.closure (⋃ i, Xs i)
-/
lemma closure_biUnion_closure_eq_closure_biUnion (M : Matroid α) (Xs : ι → Set α) (A : Set ι) :
    M.closure (⋃ i ∈ A, M.closure (Xs i)) = M.closure (⋃ i ∈ A, Xs i) := by
  rw [biUnion_eq_iUnion, M.closure_iUnion_closure_eq_closure_iUnion, biUnion_eq_iUnion]
/-
**Matroid.closure_biUnion_congr** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_biUnion_congr (M : Matroid α) (Xs Ys : ι -> Set α) (A : Set ι) (h 
: forall i in A, M.closure (Xs i) = M.closure (Ys i)) : M.closure (⋃ i in A, Xs 
i) = M.closure (⋃ i in A, Ys i)
参数：M : Matroid α；Xs Ys : ι -> Set α；A : Set ι；h : forall i in A, M.closure (Xs i
) = M.closure (Ys i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_biUnion_closure_eq_closure_biUnion`：closure_biUnion_clos
ure_eq_closure_biUnion (M : Matroid α) (Xs : ι -> Set α) (A : Set ι) : M.closure
 (⋃ i in A, M.closure (Xs i)) = M.closur…
· 使用引理 `Set.iUnion₂_congr`：iUnion₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋃ (i) (j), s i j = ⋃ (i) (j), t i j
-/
lemma closure_biUnion_congr (M : Matroid α) (Xs Ys : ι → Set α) (A : Set ι)
    (h : ∀ i ∈ A, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i ∈ A, Xs i) = M.closure (⋃ i ∈ A, Ys i) := by
  rw [← closure_biUnion_closure_eq_closure_biUnion, iUnion₂_congr h,
    closure_biUnion_closure_eq_closure_biUnion]
/-
**Matroid.closure_closure_union_closure_eq_closure_union** 是 Mathlib 中的一个引理，位于命名
空间 `Matroid`。
形式化陈述：closure_closure_union_closure_eq_closure_union (M : Matroid α) (X Y : Set 
α) : M.closure (M.closure X union M.closure Y) = M.closure (X union Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_iUnion_closure_eq_closure_iUnion`：closure_iUnion_closure
_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α) : M.closure (⋃ i, M.closure
 (Xs i)) = M.closure (⋃ i, Xs i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.cond_eq_ite`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif b then t e
lse e) = if b = true then t else e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma closure_closure_union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [eq_comm, union_eq_iUnion, ← closure_iUnion_closure_eq_closure_iUnion, union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]
/-
**Matroid.closure_union_closure_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X Y : Set α), M.closure (X ∪ M.closure Y
) = M.closure (X ∪ Y)
参数：M : Matroid α；X Y : Set α；X ∪ M.closure Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_closure_union_closure_eq_closure_union`：closure_closure_
union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) : M.closure (M.clos
ure X union M.closure Y) = M.closure (X unio…
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
@[simp] lemma closure_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]
/-
**Matroid.closure_union_closure_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X Y : Set α), M.closure (M.closure X ∪ Y
) = M.closure (X ∪ Y)
参数：M : Matroid α；X Y : Set α；M.closure X ∪ Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_closure_union_closure_eq_closure_union`：closure_closure_
union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) : M.closure (M.clos
ure X union M.closure Y) = M.closure (X unio…
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
@[simp] lemma closure_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]
/-
**Matroid.closure_insert_closure_eq_closure_insert** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (e : α) (X : Set α), M.closure (insert e 
(M.closure X)) = M.closure (insert e X)
参数：M : Matroid α；e : α；X : Set α；insert e (M.closure X)；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma closure_insert_closure_eq_closure_insert (M : Matroid α) (e : α) (X : Set α) :
    M.closure (insert e (M.closure X)) = M.closure (insert e X) := by
  simp_rw [← singleton_union, closure_union_closure_right_eq]
/-
**Matroid.closure_union_congr_left** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_union_congr_left {X' : Set α} (h : M.closure X = M.closure X') : M
.closure (X union Y) = M.closure (X' union Y)
参数：h : M.closure X = M.closure X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_union_closure_left_eq`：∀ {α : Type u_2} (M : Matroid α) 
(X Y : Set α), M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y)
-/
lemma closure_union_congr_left {X' : Set α} (h : M.closure X = M.closure X') :
    M.closure (X ∪ Y) = M.closure (X' ∪ Y) := by
  rw [← M.closure_union_closure_left_eq, h, M.closure_union_closure_left_eq]
/-
**Matroid.closure_union_congr_right** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_union_congr_right {Y' : Set α} (h : M.closure Y = M.closure Y') : 
M.closure (X union Y) = M.closure (X union Y')
参数：h : M.closure Y = M.closure Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
-/
lemma closure_union_congr_right {Y' : Set α} (h : M.closure Y = M.closure Y') :
    M.closure (X ∪ Y) = M.closure (X ∪ Y') := by
  rw [← M.closure_union_closure_right_eq, h, M.closure_union_closure_right_eq]
/-
**Matroid.closure_insert_congr_right** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_insert_congr_right (h : M.closure X = M.closure Y) : M.closure (in
sert e X) = M.closure (insert e Y)
参数：h : M.closure X = M.closure Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.closure_union_congr_left`：closure_union_congr_left {X' : Set α} 
(h : M.closure X = M.closure X') : M.closure (X union Y) = M.closure (X' union Y
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma closure_insert_congr_right (h : M.closure X = M.closure Y) :
    M.closure (insert e X) = M.closure (insert e Y) := by
  simp [← union_singleton, closure_union_congr_left h]
/-
**Matroid.closure_union_closure_empty_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.closure X ∪ M.closure ∅ = 
M.closure X
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
@[simp] lemma closure_union_closure_empty_eq (M : Matroid α) (X : Set α) :
    M.closure X ∪ M.closure ∅ = M.closure X :=
  union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))
/-
**Matroid.closure_empty_union_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M.closure ∅ ∪ M.closure X = 
M.closure X
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
@[simp] lemma closure_empty_union_closure_eq (M : Matroid α) (X : Set α) :
    M.closure ∅ ∪ M.closure X = M.closure X :=
  union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))
/-
**Matroid.closure_insert_eq_of_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_insert_eq_of_mem_closure (he : e in M.closure X) : M.closure (inse
rt e X) = M.closure X
参数：he : e in M.closure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma closure_insert_eq_of_mem_closure (he : e ∈ M.closure X) :
    M.closure (insert e X) = M.closure X := by
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem he, closure_closure]
/-
**Matroid.mem_closure_self** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_self (M : Matroid α) (e : α) (he : e in M.E
参数：M : Matroid α；e : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
-/
lemma mem_closure_self (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure {e} :=
  mem_closure_of_mem' M rfl

section Indep

variable {ι : Sort*} {I J B : Set α} {x : α}

/-
**Matroid.Indep.closure_eq_setOfPred_isBasis_insert** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Indep I → M.closure I = {x
 | M.IsBasis I (insert x I)}
参数：insert x I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.isBasis_setOfPred_insert_isBasis`：∀ {α : Type u_1} {M : Ma
troid α} {I : Set α}, M.Indep I → M.IsBasis I {x | M.IsBasis I (insert x I)}
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Matroid.IsBasis.isBasis_of_isBasis_of_subset_of_subset`：∀ {α : Type u_1}
 {M : Matroid α} {I X Y J : Set α}, M.IsBasis I X → M.IsBasis J Y → J ⊆ X → I ⊆ 
Y → M.IsBasis I Y
· 使用定理 `Matroid.IsBasis.isBasis_union`：∀ {α : Type u_1} {M : Matroid α} {I X Y :
 Set α}, M.IsBasis I X → M.IsBasis I Y → M.IsBasis I (X ∪ Y)
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用引理 `Matroid.closure_def`：closure_def (M : Matroid α) (X : Set α) : M.closure
 X = ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F}
· 使用定理 `Set.subset_sInter_iff`：subset_sInter_iff {S : Set (Set α)} {t : Set α} :
 t subseteq ⋂₀ S ↔ forall t' in S, t subseteq t'
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Matroid.IsFlat.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {F : Set 
α}, M.IsFlat F → F ⊆ M.E
· 使用定理 `Matroid.IsFlat.subset_of_isBasis_of_isBasis`：∀ {α : Type u_2} {M : Matro
id α} {F : Set α}, M.IsFlat F → ∀ ⦃I X : Set α⦄, M.IsBasis I F → M.IsBasis I X →
 X ⊆ F
· 使用定理 `Matroid.IsBasis.isBasis_union_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → M.IsBasis J (J ∪ X)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma Indep.closure_eq_setOfPred_isBasis_insert (hI : M.Indep I) :
    M.closure I = {x | M.IsBasis I (insert x I)} := by
  set F := {x | M.IsBasis I (insert x I)}
  have hIF : M.IsBasis I F := hI.isBasis_setOfPred_insert_isBasis
  have hF : M.IsFlat F := by
    refine ⟨fun J X hJF hJX e heX ↦ show M.IsBasis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.isBasis_of_isBasis_of_subset_of_subset (hJX.isBasis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).isBasis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))
  rw [subset_antisymm_iff, closure_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.IsBasis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.isBasis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

@[deprecated (since := "2026-07-09")]
alias Indep.closure_eq_setOf_isBasis_insert := Indep.closure_eq_setOfPred_isBasis_insert
/-
**Matroid.Indep.insert_isBasis_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → (M.IsBas
is I (insert e I) ↔ e ∈ M.closure I)
参数：M.IsBasis I (insert e I) ↔ e ∈ M.closure I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.closure_eq_setOfPred_isBasis_insert`：∀ {α : Type u_2} {M :
 Matroid α} {I : Set α}, M.Indep I → M.closure I = {x | M.IsBasis I (insert x I)
}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.insert_isBasis_iff_mem_closure (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ e ∈ M.closure I := by
  rw [hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred]
/-
**Matroid.Indep.isBasis_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Indep I → M.IsBasis I (M.c
losure I)
参数：M.closure I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.closure_eq_setOfPred_isBasis_insert`：∀ {α : Type u_2} {M :
 Matroid α} {I : Set α}, M.Indep I → M.closure I = {x | M.IsBasis I (insert x I)
}
· 使用定理 `Matroid.Indep.isBasis_setOfPred_insert_isBasis`：∀ {α : Type u_1} {M : Ma
troid α} {I : Set α}, M.Indep I → M.IsBasis I {x | M.IsBasis I (insert x I)}
-/
lemma Indep.isBasis_closure (hI : M.Indep I) : M.IsBasis I (M.closure I) := by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; exact hI.isBasis_setOfPred_insert_isBasis
/-
**Matroid.IsBasis.closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`
。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I X → M.closure 
I = M.closure X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
· 使用定理 `Matroid.Indep.closure_eq_setOfPred_isBasis_insert`：∀ {α : Type u_2} {M :
 Matroid α} {I : Set α}, M.Indep I → M.closure I = {x | M.IsBasis I (insert x I)
}
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
lemma IsBasis.closure_eq_closure (h : M.IsBasis I X) : M.closure I = M.closure X := by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I, h.indep.closure_eq_setOfPred_isBasis_insert]
  exact M.closure_subset_closure fun e he ↦ (h.isBasis_subset (subset_insert _ _)
    (insert_subset he h.subset))
/-
**Matroid.IsBasis.closure_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I (M.closure X) 
→ M.closure I = M.closure X
参数：M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma IsBasis.closure_eq_right (h : M.IsBasis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure
/-
**Matroid.IsBasis'.closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis
'`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis' I X → M.closure
 I = M.closure X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
lemma IsBasis'.closure_eq_closure (h : M.IsBasis' I X) : M.closure I = M.closure X := by
  rw [← closure_inter_ground _ X, h.isBasis_inter_ground.closure_eq_closure]
/-
**Matroid.IsBasis.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I X → X ⊆ M.clos
ure I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_subset_closure_iff_subset_closure`：closure_subset_closur
e_iff_subset_closure (hX : X subseteq M.E
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma IsBasis.subset_closure (h : M.IsBasis I X) : X ⊆ M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure, h.closure_eq_closure]
/-
**Matroid.IsBasis'.isBasis_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBa
sis'`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis' I X → M.IsBasis
 I (M.closure X)
参数：M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Matroid.Indep.isBasis_closure`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α}, M.Indep I → M.IsBasis I (M.closure I)
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
-/
lemma IsBasis'.isBasis_closure_right (h : M.IsBasis' I X) : M.IsBasis I (M.closure X) := by
  rw [← h.closure_eq_closure]; exact h.indep.isBasis_closure
/-
**Matroid.IsBasis.isBasis_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I X → M.IsBasis 
I (M.closure X)
参数：M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.isBasis_closure_right (h : M.IsBasis I X) : M.IsBasis I (M.closure X) :=
  h.isBasis'.isBasis_closure_right
/-
**Matroid.Indep.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α} {x : α}, M.Indep I → (x ∈ M.c
losure I ↔ M.Dep (insert x I) ∨ x ∈ I)
参数：x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.closure_eq_setOfPred_isBasis_insert`：∀ {α : Type u_2} {M :
 Matroid α} {I : Set α}, M.Indep I → M.closure I = {x | M.IsBasis I (insert x I)
}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Matroid.Indep.isBasis_insert_iff`：∀ {α : Type u_1} {M : Matroid α} {I : 
Set α} {e : α},   M.Indep I → (M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e
 ∈ I)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.mem_closure_iff (hI : M.Indep I) :
    x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I := by
  rwa [hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred, isBasis_insert_iff]
/-
**Matroid.Indep.mem_closure_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α} {x : α},   M.Indep I → (x ∈ M
.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I))
参数：x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Indep.mem_closure_iff' (hI : M.Indep I) :
    x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I) := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground,
    imp_iff_not_or]
  have := hI.subset_ground
  aesop
/-
**Matroid.Indep.insert_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → (M.Dep (
insert e I) ↔ e ∈ M.closure I \ I)
参数：M.Dep (insert e I) ↔ e ∈ M.closure I \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `and_not_self_iff`：∀ (a : Prop), a ∧ ¬a ↔ False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
-/
lemma Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e ∈ M.closure I \ I := by
  rw [mem_sdiff, hI.mem_closure_iff, or_and_right, and_not_self_iff, or_false,
    iff_self_and, imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep
/-
**Matroid.Indep.mem_closure_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Ind
ep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → e ∉ I → 
(e ∈ M.closure I ↔ M.Dep (insert e I))
参数：e ∈ M.closure I ↔ M.Dep (insert e I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.insert_dep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α} {
I : Set α}, M.Indep I → (M.Dep (insert e I) ↔ e ∈ M.closure I \ I)
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.mem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.closure I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_sdiff, and_iff_left heI]
/-
**Matroid.Indep.notMem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α},   M.Indep I →     au
toParam (e ∈ M.E) Matroid.Indep.notMem_closure_iff._auto_1 → (e ∉ M.closure I ↔ 
M.Indep (insert e I) ∧ e ∉ I)
参数：e ∈ M.E；e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma Indep.notMem_closure_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) :
    e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_right he,
    and_iff_left hI.subset_ground]; tauto
/-
**Matroid.Indep.notMem_closure_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α},   M.Indep I →     e 
∉ I →       autoParam (e ∈ M.E) Matroid.Indep.notMem_closure_iff_of_notMem._auto
_1 → (e ∉ M.closure I ↔ M.Indep (insert e I))
参数：e ∈ M.E；e ∉ M.closure I ↔ M.Indep (insert e I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.notMem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {e : 
α} {I : Set α},   M.Indep I →     autoParam (e ∈ M.E) Matroid.Indep.notMem_closu
re_iff._auto_1 → (e ∉ …
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.notMem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I)
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.closure I ↔ M.Indep (insert e I) := by
  rw [hI.notMem_closure_iff, and_iff_left heI]
/-
**Matroid.Indep.insert_indep_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.In
dep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → e ∉ I → 
(M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I)
参数：M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Matroid.Indep.mem_closure_iff_of_notMem`：∀ {α : Type u_2} {M : Matroid α
} {e : α} {I : Set α}, M.Indep I → e ∉ I → (e ∈ M.closure I ↔ M.Dep (insert e I)
)
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Indep.insert_indep_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I := by
  rw [mem_sdiff, hI.mem_closure_iff_of_notMem heI, dep_iff, not_and, not_imp_not, insert_subset_iff,
    and_iff_left hI.subset_ground]
  exact ⟨fun h ↦ ⟨h.subset_ground (mem_insert e I), fun _ ↦ h⟩, fun h ↦ h.2 h.1⟩
/-
**Matroid.Indep.insert_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → (M.Indep
 (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I)
参数：M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Matroid.Indep.insert_indep_iff_of_notMem`：∀ {α : Type u_2} {M : Matroid 
α} {e : α} {I : Set α}, M.Indep I → e ∉ I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.
closure I)
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I := by
  obtain (h | h) := em (e ∈ I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_notMem h, or_iff_left h]
/-
**Matroid.insert_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I -> e in M.E \
 M.closure I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.insert_indep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I → e ∈ M.E \ M.closure I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI <| h.subset <| subset_insert _ _]

/-- This can be used for rewriting if the LHS is inside a binder and it is unknown
whether `f = e`. -/
/-
**Matroid.Indep.insert_sdiff_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`
。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e f : α} {I : Set α},   M.Indep (I \ {e}
) → e ∈ I → (M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I)
参数：I \ {e}；M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Matroid.Indep.insert_indep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I)
· 使用引理 `Set.mem_sdiff_singleton`：mem_sdiff_singleton : a in s \ {b} ↔ a in s ∧ a
 != b
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
This can be used for rewriting if the LHS is inside a binder and it is unknown
whether `f = e`.
-/
lemma Indep.insert_sdiff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I := by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_sdiff_singleton_comm hne.symm, hI.insert_indep_iff, mem_sdiff_singleton,
    and_iff_left hne.symm]

@[deprecated (since := "2026-06-03")]
alias Indep.insert_diff_indep_iff := Indep.insert_sdiff_indep_iff
/-
**Matroid.Indep.isBasis_of_subset_of_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.
closure I → M.IsBasis I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Matroid.Indep.isBasis_closure`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α}, M.Indep I → M.IsBasis I (M.closure I)
-/
lemma Indep.isBasis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : X ⊆ M.closure I) : M.IsBasis I X :=
  hI.isBasis_closure.isBasis_subset hIX hXI
/-
**Matroid.isBasis_iff_indep_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff_indep_subset_closure : M.IsBasis I X ↔ M.Indep I ∧ I subseteq 
X ∧ X subseteq M.closure I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isBasis_iff_indep_subset_closure : M.IsBasis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h ↦ h.1.isBasis_of_subset_of_subset_closure h.2.1 h.2.2⟩
/-
**Matroid.Indep.isBase_of_ground_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Indep I → M.E ⊆ M.closure 
I → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma Indep.isBase_of_ground_subset_closure (hI : M.Indep I) (h : M.E ⊆ M.closure I) :
    M.IsBase I := by
  rw [← isBasis_ground_iff]; exact hI.isBasis_of_subset_of_subset_closure hI.subset_ground h
/-
**Matroid.IsBase.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M.IsBase B → M.closure B = M
.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.closure_ground`：∀ {α : Type u_2} (M : Matroid α), M.closure M.E 
= M.E
-/
lemma IsBase.closure_eq (hB : M.IsBase B) : M.closure B = M.E := by
  rw [← isBasis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]
/-
**Matroid.IsBase.closure_of_superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X B : Set α}, M.IsBase B → B ⊆ X → M.clo
sure X = M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
-/
lemma IsBase.closure_of_superset (hB : M.IsBase B) (hBX : B ⊆ X) : M.closure X = M.E :=
  (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)
/-
**Matroid.isBase_iff_indep_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBase_iff_indep_closure_eq : M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用引理 `Matroid.isBasis_iff_indep_subset_closure`：isBasis_iff_indep_subset_closu
re : M.IsBasis I X ↔ M.Indep I ∧ I subseteq X ∧ X subseteq M.closure I
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
lemma isBase_iff_indep_closure_eq : M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← isBasis_ground_iff, isBasis_iff_indep_subset_closure, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.closure_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩
/-
**Matroid.IsBase.exchange_base_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsBase`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e f : α} {B : Set α},   M.IsBase B →    
 e ∈ B →       f ∉ M.closure (B \ {e}) →         autoParam (f ∈ M.E) Matroid.IsB
ase.exchange_base_of_notMem_closure._auto_1 → M.IsBase (insert f (B \ {e}))
参数：B \ {e}；f ∈ M.E；insert f (B \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.Indep.notMem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {e : 
α} {I : Set α},   M.Indep I →     autoParam (e ∈ M.E) Matroid.Indep.notMem_closu
re_iff._auto_1 → (e ∉ …
· 使用定理 `Matroid.Indep.sdiff`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Ind
ep I → ∀ (X : Set α), M.Indep (I \ X)
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matroid.IsBase.exchange_isBase_of_indep`：∀ {α : Type u_1} {M : Matroid α
} {B : Set α} {e f : α},   M.IsBase B → f ∉ B → M.Indep (insert f (B \ {e})) → M
.IsBase (insert f (B \ {e}))
-/
lemma IsBase.exchange_base_of_notMem_closure (hB : M.IsBase B) (he : e ∈ B)
    (hf : f ∉ M.closure (B \ {e})) (hfE : f ∈ M.E := by aesop_mat) :
    M.IsBase (insert f (B \ {e})) := by
  obtain rfl | hne := eq_or_ne f e
  · simpa [he]
  have ⟨hi, hfB⟩ : M.Indep (insert f (B \ {e})) ∧ f ∉ B := by
    simpa [(hB.indep.sdiff _).notMem_closure_iff, hne] using hf
  exact hB.exchange_isBase_of_indep hfB hi
/-
**Matroid.Indep.isBase_iff_ground_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Indep I → (M.IsBase I ↔ M.
E ⊆ M.closure I)
参数：M.IsBase I ↔ M.E ⊆ M.closure I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用定理 `Matroid.Indep.isBase_of_ground_subset_closure`：∀ {α : Type u_2} {M : Mat
roid α} {I : Set α}, M.Indep I → M.E ⊆ M.closure I → M.IsBase I
-/
lemma Indep.isBase_iff_ground_subset_closure (hI : M.Indep I) : M.IsBase I ↔ M.E ⊆ M.closure I :=
  ⟨fun h ↦ h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure⟩
/-
**Matroid.Indep.closure_inter_eq_self_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I J : Set α}, M.Indep I → J ⊆ I → M.clos
ure J ∩ I = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `Matroid.Indep.isBasis_closure`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α}, M.Indep I → M.IsBasis I (M.closure I)
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) :
    M.closure J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.isBasis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

/-- For a nonempty collection of subsets of a given independent set,
the closure of the intersection is the intersection of the closure. -/
/-
**Matroid.Indep.closure_sInter_eq_biInter_closure_of_forall_subset** 是 Mathlib 中
的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α} {Js : Set (Set α)},   M.Indep
 I → Js.Nonempty → (∀ J ∈ Js, J ⊆ I) → M.closure (⋂₀ Js) = ⋂ J ∈ Js, M.closure J
参数：Set α；∀ J ∈ Js, J ⊆ I；⋂₀ Js。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `Set.subset_iInter₂_iff`：subset_iInter₂_iff {s : Set α} {t : forall i, κ 
i -> Set α} : (s subseteq ⋂ (i) (j), t i j) ↔ forall i j, s subseteq t i j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用引理 `Matroid.mem_closure_of_mem`：mem_closure_of_mem (M : Matroid α) (h : e in
 X) (hX : X subseteq M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.closure_inter_eq_self_of_subset`：∀ {α : Type u_2} {M : Mat
roid α} {I J : Set α}, M.Indep I → J ⊆ I → M.closure J ∩ I = J
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.Indep.notMem_closure_iff_of_notMem`：∀ {α : Type u_2} {M : Matroi
d α} {e : α} {I : Set α},   M.Indep I →     e ∉ I →       autoParam (e ∈ M.E) Ma
troid.Indep.notMem_closure_iff_o…
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.Indep.insert_isBasis_iff_mem_closure`：∀ {α : Type u_2} {M : Matr
oid α} {e : α} {I : Set α}, M.Indep I → (M.IsBasis I (insert e I) ↔ e ∈ M.closur
e I)
· 使用定理 `Matroid.IsBasis.exchange`：∀ {α : Type u_1} {M : Matroid α} {I X J : Set 
α} {e : α},   M.IsBasis I X → M.IsBasis J X → e ∈ I \ J → ∃ f ∈ J \ I, M.IsBasis
 (insert f (I …
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
For a nonempty collection of subsets of a given independent set,
the closure of the intersection is the intersection of the closure.
-/
lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.closure (⋂₀ Js) = (⋂ J ∈ Js, M.closure J) := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX ↦ M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he ↦ by_contra fun he' ↦ ?_⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I := by
    refine ⟨M.closure_subset_ground _ (he _ hne.some_mem), fun heI ↦ he' ?_⟩
    refine mem_closure_of_mem _ (fun X hX' ↦ ?_) hiI.subset_ground
    rw [← hI.closure_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩
  rw [hiI.notMem_closure_iff_of_notMem (notMem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_isBasis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)
  have hIb : M.IsBasis I (insert e I) := by
    rw [hI.insert_isBasis_iff_mem_closure]
    exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)
  obtain ⟨f, hfIJ, hfb⟩ := hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_isBasis (hfb.isBasis_subset (insert_subset hfIJ.1
    (by (rw [sdiff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))
  refine hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ ?_))
  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_closure_iff).mp (he _ hX')
  · refine (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) ?_)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union, ← sdiff_subset_iff, sdiff_singleton_eq_self hfX] at hIs
    exact hIs.trans sdiff_subset
  exact heEI.2 (hIs _ hX' heX)
/-
**Matroid.closure_iInter_eq_iInter_closure_of_iUnion_indep** 是 Mathlib 中的一个引理，位于
命名空间 `Matroid`。
形式化陈述：closure_iInter_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι
 -> Set α) (h : M.Indep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ i, M.closure (
Is i))
参数：Is : ι -> Set α；h : M.Indep (⋃ i, Is i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matroid.Indep.closure_sInter_eq_biInter_closure_of_forall_subset`：∀ {α :
 Type u_2} {M : Matroid α} {I : Set α} {Js : Set (Set α)},   M.Indep I → Js.None
mpty → (∀ J ∈ Js, J ⊆ I) → M.closure (⋂₀ Js) = ⋂ J ∈ J…
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma closure_iInter_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι → Set α)
    (h : M.Indep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by
  convert!
    h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
      (by simp [subset_iUnion])
  simp
/-
**Matroid.closure_sInter_eq_biInter_closure_of_sUnion_indep** 是 Mathlib 中的一个引理，位
于命名空间 `Matroid`。
形式化陈述：closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs 
: Is.Nonempty) (h : M.Indep (⋃₀ Is)) : M.closure (⋂₀ Is) = (⋂ I in Is, M.closure
 I)
参数：Is : Set (Set α)；hIs : Is.Nonempty；h : M.Indep (⋃₀ Is)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.closure_sInter_eq_biInter_closure_of_forall_subset`：∀ {α :
 Type u_2} {M : Matroid α} {I : Set α} {Js : Set (Set α)},   M.Indep I → Js.None
mpty → (∀ J ∈ Js, J ⊆ I) → M.closure (⋂₀ Js) = ⋂ J ∈ J…
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
lemma closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) : M.closure (⋂₀ Is) = (⋂ I ∈ Is, M.closure I) :=
  h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ ↦ subset_sUnion_of_mem)
/-
**Matroid.closure_biInter_eq_biInter_closure_of_biUnion_indep** 是 Mathlib 中的一个引理
，位于命名空间 `Matroid`。
形式化陈述：closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι
} (hA : A.Nonempty) {I : ι -> Set α} (h : M.Indep (⋃ i in A, I i)) : M.closure (
⋂ i in A, I i) = ⋂ i in A, M.closure (I i)
参数：hA : A.Nonempty；h : M.Indep (⋃ i in A, I i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matroid.closure_iInter_eq_iInter_closure_of_iUnion_indep`：closure_iInter
_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι -> Set α) (h : M.In
dep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ …
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
-/
lemma closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι → Set α} (h : M.Indep (⋃ i ∈ A, I i)) :
    M.closure (⋂ i ∈ A, I i) = ⋂ i ∈ A, M.closure (I i) := by
  have := hA.coe_sort
  convert! closure_iInter_eq_iInter_closure_of_iUnion_indep (Is := fun i : A ↦ I i) (by simpa) <;>
  simp
/-
**Matroid.Indep.closure_iInter_eq_biInter_closure_of_forall_subset** 是 Mathlib 中
的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {ι : Sort u_3} {I : Set α} [Nonempty ι] {
Js : ι → Set α},   M.Indep I → (∀ (i : ι), Js i ⊆ I) → M.closure (⋂ i, Js i) = ⋂
 i, M.closure (Js i)
参数：∀ (i : ι), Js i ⊆ I；⋂ i, Js i；Js i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_iInter_eq_iInter_closure_of_iUnion_indep`：closure_iInter
_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι -> Set α) (h : M.In
dep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ …
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
-/
lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset [Nonempty ι] {Js : ι → Set α}
    (hI : M.Indep I) (hJs : ∀ i, Js i ⊆ I) : M.closure (⋂ i, Js i) = ⋂ i, M.closure (Js i) :=
  closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)
/-
**Matroid.Indep.closure_inter_eq_inter_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I J : Set α}, M.Indep (I ∪ J) → M.closur
e (I ∩ J) = M.closure I ∩ M.closure J
参数：I ∪ J；I ∩ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_iInter`：inter_eq_iInter {s₁ s₂ : Set α} : s₁ inter s₂ = ⋂ b
 : Bool, cond b s₁ s₂
· 使用引理 `Matroid.closure_iInter_eq_iInter_closure_of_iUnion_indep`：closure_iInter
_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι -> Set α) (h : M.In
dep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Indep.closure_inter_eq_inter_closure (h : M.Indep (I ∪ J)) :
    M.closure (I ∩ J) = M.closure I ∩ M.closure J := by
  rw [inter_eq_iInter, closure_iInter_eq_iInter_closure_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]
/-
**Matroid.Indep.inter_isBasis_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α} {ι : Type u_4},   M.Indep I →
     ∀ {X : ι → Set α} {A : Set ι},       A.Nonempty → (∀ i ∈ A, M.IsBasis (X i 
∩ I) (X i)) → M.IsBasis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i)
参数：∀ i ∈ A, M.IsBasis (X i ∩ I) (X i)；(⋂ i ∈ A, X i) ∩ I；⋂ i ∈ A, X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.Indep.inter_left`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, 
M.Indep I → ∀ (X : Set α), M.Indep (X ∩ I)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biInter_inter`：biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonem
pty) (f : ι -> Set α) (t : Set α) : ⋂ i in s, f i inter t = (⋂ i in s, f i) inte
r t
· 使用引理 `Matroid.closure_biInter_eq_biInter_closure_of_biUnion_indep`：closure_biI
nter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempt
y) {I : ι -> Set α} (h : M.Indep (⋃ i in A, I i))…
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
-/
lemma Indep.inter_isBasis_biInter {ι : Type*} (hI : M.Indep I) {X : ι → Set α} {A : Set ι}
    (hA : A.Nonempty) (h : ∀ i ∈ A, M.IsBasis ((X i) ∩ I) (X i)) :
    M.IsBasis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  simp_rw [← biInter_inter hA,
  closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure
/-
**Matroid.Indep.inter_isBasis_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {ι : Sort u_3} {I : Set α} [Nonempty ι] {
X : ι → Set α},   M.Indep I → (∀ (i : ι), M.IsBasis (X i ∩ I) (X i)) → M.IsBasis
 ((⋂ i, X i) ∩ I) (⋂ i, X i)
参数：∀ (i : ι), M.IsBasis (X i ∩ I) (X i)；(⋂ i, X i) ∩ I；⋂ i, X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `Set.iInter_plift_down`：iInter_plift_down (f : ι -> Set α) : ⋂ i, f (PLif
t.down i) = ⋂ i, f i
· 使用定理 `Matroid.Indep.inter_isBasis_biInter`：∀ {α : Type u_2} {M : Matroid α} {I
 : Set α} {ι : Type u_4},   M.Indep I →     ∀ {X : ι → Set α} {A : Set ι},      
 A.Nonempty → (∀ i ∈ A, M…
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `PLift.instNonempty_mathlib`：∀ {α : Sort u} [Nonempty α], Nonempty (PLift
 α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma Indep.inter_isBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.IsBasis ((X i) ∩ I) (X i)) : M.IsBasis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  convert!
    hI.inter_isBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i ↦ X i.down)
      (by simpa using fun (i : PLift ι) ↦ h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm
/-
**Matroid.Indep.inter_isBasis_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α} {Xs : Set (Set α)},   M.Indep
 I → Xs.Nonempty → (∀ X ∈ Xs, M.IsBasis (X ∩ I) X) → M.IsBasis (⋂₀ Xs ∩ I) (⋂₀ X
s)
参数：Set α；∀ X ∈ Xs, M.IsBasis (X ∩ I) X；⋂₀ Xs ∩ I；⋂₀ Xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Matroid.Indep.inter_isBasis_biInter`：∀ {α : Type u_2} {M : Matroid α} {I
 : Set α} {ι : Type u_4},   M.Indep I →     ∀ {X : ι → Set α} {A : Set ι},      
 A.Nonempty → (∀ i ∈ A, M…
-/
lemma Indep.inter_isBasis_sInter {Xs : Set (Set α)} (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.IsBasis (X ∩ I) X) : M.IsBasis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.inter_isBasis_biInter hXs h
/-
**Matroid.isBasis_iff_isBasis_closure_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Matro
id`。
形式化陈述：isBasis_iff_isBasis_closure_of_subset (hIX : I subseteq X) (hX : X subsete
q M.E
参数：hIX : I subseteq X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
-/
lemma isBasis_iff_isBasis_closure_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) :=
  ⟨fun h ↦ h.isBasis_closure_right, fun h ↦ h.isBasis_subset hIX (M.subset_closure X hX)⟩
/-
**Matroid.isBasis_iff_isBasis_closure_of_subset'** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：isBasis_iff_isBasis_closure_of_subset' (hIX : I subseteq X) : M.IsBasis I 
X ↔ M.IsBasis I (M.closure X) ∧ X subseteq M.E
参数：hIX : I subseteq X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isBasis_iff_isBasis_closure_of_subset' (hIX : I ⊆ X) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.isBasis_closure_right, h.subset_ground⟩,
    fun h ↦ h.1.isBasis_subset hIX (M.subset_closure X h.2)⟩
/-
**Matroid.isBasis'_iff_isBasis_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis' I X ↔ M.IsBasis
 I (M.closure X) ∧ I ⊆ X
参数：M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isBasis'_iff_isBasis_closure : M.IsBasis' I X ↔ M.IsBasis I (M.closure X) ∧ I ⊆ X := by
  rw [← closure_inter_ground, isBasis'_iff_isBasis_inter_ground]
  exact ⟨fun h ↦ ⟨h.isBasis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h ↦ h.1.isBasis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩
/-
**Matroid.exists_isBasis_inter_ground_isBasis_closure** 是 Mathlib 中的一个引理，位于命名空间 
`Matroid`。
形式化陈述：exists_isBasis_inter_ground_isBasis_closure (M : Matroid α) (X : Set α) : 
exists I, M.IsBasis I (X inter M.E) ∧ M.IsBasis I (M.closure X)
参数：M : Matroid α；X : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
-/
lemma exists_isBasis_inter_ground_isBasis_closure (M : Matroid α) (X : Set α) :
    ∃ I, M.IsBasis I (X ∩ M.E) ∧ M.IsBasis I (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  have hI' := hI.isBasis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩
/-
**Matroid.IsBasis.isBasis_of_closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X Y I : Set α},   M.IsBasis I X →     I 
⊆ Y →       M.closure X = M.closure Y →         autoParam (Y ⊆ M.E) Matroid.IsBa
sis.isBasis_of_closure_eq_closure._auto_1 → M.IsBasis I Y
参数：Y ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
-/
lemma IsBasis.isBasis_of_closure_eq_closure (hI : M.IsBasis I X) (hY : I ⊆ Y)
    (h : M.closure X = M.closure Y) (hYE : Y ⊆ M.E := by aesop_mat) : M.IsBasis I Y := by
  refine hI.indep.isBasis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure, h]
  exact M.subset_closure Y
/-
**Matroid.isBasis_union_iff_indep_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBasis_union_iff_indep_closure : M.IsBasis I (I union X) ↔ M.Indep I ∧ X 
subseteq M.closure I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Matroid.Indep.isBasis_closure`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α}, M.Indep I → M.IsBasis I (M.closure I)
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma isBasis_union_iff_indep_closure : M.IsBasis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ ↦
    hI.isBasis_closure.isBasis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩
/-
**Matroid.isBasis_iff_indep_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff_indep_closure : M.IsBasis I X ↔ M.Indep I ∧ X subseteq M.closu
re I ∧ I subseteq X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.isBasis_union_iff_indep_closure`：isBasis_union_iff_indep_closure
 : M.IsBasis I (I union X) ↔ M.Indep I ∧ X subseteq M.closure I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
lemma isBasis_iff_indep_closure : M.IsBasis I X ↔ M.Indep I ∧ X ⊆ M.closure I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_closure, h.subset⟩, fun h ↦
    (isBasis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).isBasis_subset h.2.2 subset_union_right⟩
/-
**Matroid.Indep.inter_isBasis_closure_iff_subset_closure_inter** 是 Mathlib 中的一个定
理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I X : Set α}, M.Indep I → (M.IsBasis (X 
∩ I) X ↔ X ⊆ M.closure (X ∩ I))
参数：M.IsBasis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.Indep.inter_left`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, 
M.Indep I → ∀ (X : Set α), M.Indep (X ∩ I)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma Indep.inter_isBasis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.IsBasis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I) :=
  ⟨IsBasis.subset_closure, (hI.inter_left X).isBasis_of_subset_of_subset_closure inter_subset_left⟩
/-
**Matroid.IsBasis.closure_inter_isBasis_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α},   M.IsBasis (X ∩ I) X → M.
Indep I → M.IsBasis (M.closure X ∩ I) (M.closure X)
参数：X ∩ I；M.closure X ∩ I；M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.inter_isBasis_closure_iff_subset_closure_inter`：∀ {α : Typ
e u_2} {M : Matroid α} {I X : Set α}, M.Indep I → (M.IsBasis (X ∩ I) X ↔ X ⊆ M.c
losure (X ∩ I))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma IsBasis.closure_inter_isBasis_closure (h : M.IsBasis (X ∩ I) X) (hI : M.Indep I) :
    M.IsBasis (M.closure X ∩ I) (M.closure X) := by
  rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))
/-
**Matroid.IsBasis.eq_of_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasi
s`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I J : Set α}, M.IsBasis I X → J ⊆ I → 
X ⊆ M.closure J → J = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.closure_inter_eq_self_of_subset`：∀ {α : Type u_2} {M : Mat
roid α} {I J : Set α}, M.Indep I → J ⊆ I → M.closure J ∩ I = J
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
lemma IsBasis.eq_of_closure_subset (hI : M.IsBasis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.closure J) :
    J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ
/-
**Matroid.IsBasis.insert_isBasis_insert_of_notMem_closure** 是 Mathlib 中的一个定理，位于命
名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α} {e : α} {I : Set α},   M.IsBa
sis I X →     e ∉ M.closure I →       autoParam (e ∈ M.E) Matroid.IsBasis.insert
_isBasis_insert_of_notMem_closure._auto_1 →         M.IsBasis (insert e I) (inse
rt e X)
参数：e ∈ M.E；insert e I；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.insert_isBasis_insert`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α} {e : α},   M.IsBasis I X → M.Indep (insert e I) → M.IsBasis (inser
t e I) (insert e X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.Indep.insert_indep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
lemma IsBasis.insert_isBasis_insert_of_notMem_closure (hIX : M.IsBasis I X) (heI : e ∉ M.closure I)
    (heE : e ∈ M.E := by aesop_mat) : M.IsBasis (insert e I) (insert e X) :=
  hIX.insert_isBasis_insert <| hIX.indep.insert_indep_iff.2 <| .inl ⟨heE, heI⟩
/-
**Matroid.empty_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α}, M.IsBasis ∅ X ↔ X ⊆ M.closur
e ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isBasis_iff_indep_closure`：isBasis_iff_indep_closure : M.IsBasis
 I X ↔ M.Indep I ∧ X subseteq M.closure I ∧ I subseteq X
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma empty_isBasis_iff : M.IsBasis ∅ X ↔ X ⊆ M.closure ∅ := by
  rw [isBasis_iff_indep_closure, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]
/-
**Matroid.indep_iff_forall_notMem_closure_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matro
id`。
形式化陈述：indep_iff_forall_notMem_closure_sdiff (hI : I subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Matroid.Indep.closure_inter_eq_self_of_subset`：∀ {α : Type u_2} {M : Mat
roid α} {I J : Set α}, M.Indep I → J ⊆ I → M.closure J ∩ I = J
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
lemma indep_iff_forall_notMem_closure_sdiff (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset sdiff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  convert! hJ.indep
  refine hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_sdiff_singleton hJ.subset heJ))

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff := indep_iff_forall_notMem_closure_sdiff

/-- An alternative version of `Matroid.indep_iff_forall_notMem_closure_sdiff` where the
hypothesis that `I ⊆ M.E` is contained in the RHS rather than the hypothesis. -/
/-
**Matroid.indep_iff_forall_notMem_closure_sdiff'** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：indep_iff_forall_notMem_closure_sdiff' : M.Indep I ↔ I subseteq M.E ∧ fora
ll e in I, e ∉ M.closure (I \ {e})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.indep_iff_forall_notMem_closure_sdiff`：indep_iff_forall_notMem_c
losure_sdiff (hI : I subseteq M.E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
An alternative version of `Matroid.indep_iff_forall_notMem_closure_sdiff` where 
the
hypothesis that `I ⊆ M.E` is contained in the RHS rather than the hypothesis.
-/
lemma indep_iff_forall_notMem_closure_sdiff' :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_forall_notMem_closure_sdiff h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_forall_notMem_closure_sdiff h.1).mpr h.2⟩

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff' := indep_iff_forall_notMem_closure_sdiff'
/-
**Matroid.Indep.notMem_closure_sdiff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
ndep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → e ∈ I → 
e ∉ M.closure (I \ {e})
参数：I \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.indep_iff_forall_notMem_closure_sdiff'`：indep_iff_forall_notMem_
closure_sdiff' : M.Indep I ↔ I subseteq M.E ∧ forall e in I, e ∉ M.closure (I \ 
{e})
-/
lemma Indep.notMem_closure_sdiff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_forall_notMem_closure_sdiff'.1 hI).2 e he

@[deprecated (since := "2026-06-03")]
alias Indep.notMem_closure_diff_of_mem := Indep.notMem_closure_sdiff_of_mem
/-
**Matroid.Indep.closure_insert_sdiff_eq_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间
 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e f : α} {I : Set α},   M.Indep I → f ∈ 
M.closure I → e ∈ M.closure (insert f I \ {e}) → M.closure (insert f I \ {e}) = 
M.closure I
参数：insert f I \ {e}；insert f I \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
-/
lemma Indep.closure_insert_sdiff_eq_of_mem_closure (hI : M.Indep I) (hf : f ∈ M.closure I)
    (he : e ∈ M.closure (insert f I \ {e})) : M.closure (insert f I \ {e}) = M.closure I := by
  apply subset_antisymm <;> apply closure_subset_closure_of_subset_closure
  · simp only [subset_def, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    rintro a (rfl | haI)
    exacts [hf, M.subset_closure _ hI.subset_ground haI]
  · intro a haI
    obtain rfl | ne := eq_or_ne a e
    exacts [he, M.mem_closure_of_mem' ⟨.inr haI, ne⟩ (hI.subset_ground haI)]

@[deprecated (since := "2026-06-03")]
alias Indep.closure_insert_diff_eq_of_mem_closure := Indep.closure_insert_sdiff_eq_of_mem_closure
/-
**Matroid.Indep.indep_insert_sdiff_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Mat
roid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e f : α} {I : Set α},   M.Indep I → f ∈ 
M.closure I → e ∈ M.closure (insert f I \ {e}) → e ∈ insert f I → M.Indep (inser
t f I \ {e})
参数：insert f I \ {e}；insert f I \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matroid.Indep.insert_sdiff_indep_iff`：∀ {α : Type u_2} {M : Matroid α} {
e f : α} {I : Set α},   M.Indep (I \ {e}) → e ∈ I → (M.Indep (insert f I \ {e}) 
↔ f ∈ M.E \ M.closure (I \…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Matroid.mem_ground_of_mem_closure`：mem_ground_of_mem_closure (he : e in 
M.closure X) : e in M.E
· 使用定理 `Matroid.Indep.notMem_closure_sdiff_of_mem`：∀ {α : Type u_2} {M : Matroid
 α} {e : α} {I : Set α}, M.Indep I → e ∈ I → e ∉ M.closure (I \ {e})
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Matroid.closure_insert_eq_of_mem_closure`：closure_insert_eq_of_mem_closu
re (he : e in M.closure X) : M.closure (insert e X) = M.closure X
-/
lemma Indep.indep_insert_sdiff_of_mem_closure (hI : M.Indep I) (hfI : f ∈ M.closure I)
    (he : e ∈ M.closure (insert f I \ {e})) (heI : e ∈ insert f I) :
    M.Indep (insert f I \ {e}) := by
  simp only [mem_insert_iff] at heI
  obtain rfl | heI := heI
  · exact hI.subset (by simp)
  rw [Indep.insert_sdiff_indep_iff (hI.subset (sdiff_subset ..)) heI]
  refine .inl ⟨mem_ground_of_mem_closure hfI, fun h ↦ hI.notMem_closure_sdiff_of_mem heI ?_⟩
  exact closure_insert_eq_of_mem_closure h ▸ M.closure_subset_closure (by intro; simp_all) he

@[deprecated (since := "2026-06-03")]
alias Indep.indep_insert_diff_of_mem_closure := Indep.indep_insert_sdiff_of_mem_closure
/-
**Matroid.IsBasis.isBasis_insert_sdiff_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 
`Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α} {e f : α} {B : Set α},   M.Is
Basis B X → e ∈ M.closure (insert f B \ {e}) → e ∈ insert f B → f ∈ X → M.IsBasi
s (insert f B \ {e}) X
参数：insert f B \ {e}；insert f B \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isBasis_iff_indep_closure`：isBasis_iff_indep_closure : M.IsBasis
 I X ↔ M.Indep I ∧ X subseteq M.closure I ∧ I subseteq X
· 使用定理 `Matroid.Indep.indep_insert_sdiff_of_mem_closure`：∀ {α : Type u_2} {M : M
atroid α} {e f : α} {I : Set α},   M.Indep I → f ∈ M.closure I → e ∈ M.closure (
insert f I \ {e}) → e ∈ insert f I → …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.closure_insert_sdiff_eq_of_mem_closure`：∀ {α : Type u_2} {
M : Matroid α} {e f : α} {I : Set α},   M.Indep I → f ∈ M.closure I → e ∈ M.clos
ure (insert f I \ {e}) → M.closure (insert…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
lemma IsBasis.isBasis_insert_sdiff_of_mem_closure (hB : M.IsBasis B X)
    (he : e ∈ M.closure (insert f B \ {e})) (heB : e ∈ insert f B) (hfX : f ∈ X) :
    M.IsBasis (insert f B \ {e}) X := by
  rw [isBasis_iff_indep_closure] at hB ⊢
  exact ⟨hB.1.indep_insert_sdiff_of_mem_closure (hB.2.1 hfX) he heB, hB.2.1.trans_eq
    (hB.1.closure_insert_sdiff_eq_of_mem_closure (hB.2.1 hfX) he).symm, sdiff_subset.trans
    (insert_subset hfX hB.2.2)⟩

@[deprecated (since := "2026-06-03")]
alias IsBasis.isBasis_insert_diff_of_mem_closure := IsBasis.isBasis_insert_sdiff_of_mem_closure
/-
**Matroid.IsBase.isBase_insert_sdiff_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.IsBase`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e f : α} {B : Set α},   M.IsBase B → e ∈
 M.closure (insert f B \ {e}) → e ∈ insert f B → M.IsBase (insert f B \ {e})
参数：insert f B \ {e}；insert f B \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.IsBasis.isBasis_insert_sdiff_of_mem_closure`：∀ {α : Type u_2} {M
 : Matroid α} {X : Set α} {e f : α} {B : Set α},   M.IsBasis B X → e ∈ M.closure
 (insert f B \ {e}) → e ∈ insert f B → f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matroid.Indep.notMem_closure_sdiff_of_mem`：∀ {α : Type u_2} {M : Matroid
 α} {e : α} {I : Set α}, M.Indep I → e ∈ I → e ∉ M.closure (I \ {e})
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
-/
lemma IsBase.isBase_insert_sdiff_of_mem_closure (hB : M.IsBase B)
    (he : e ∈ M.closure (insert f B \ {e})) (heB : e ∈ insert f B) :
    M.IsBase (insert f B \ {e}) := by
  rw [← isBasis_ground_iff] at hB ⊢
  by_cases hf : f ∈ M.E
  · exact hB.isBasis_insert_sdiff_of_mem_closure he heB hf
  obtain rfl | heB := heB
  · simpa [show e ∉ B from fun h ↦ hf (hB.1.1.2 h)] using hB
  rw [← closure_inter_ground] at he
  cases hB.indep.notMem_closure_sdiff_of_mem heB (M.closure_subset_closure (by intro; aesop) he)

@[deprecated (since := "2026-06-03")]
alias IsBase.isBase_insert_diff_of_mem_closure := IsBase.isBase_insert_sdiff_of_mem_closure
/-
**Matroid.indep_iff_forall_closure_sdiff_ne** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：indep_iff_forall_closure_sdiff_ne : M.Indep I ↔ forall ⦃e⦄, e in I -> M.cl
osure (I \ {e}) != M.closure I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.indep_iff_forall_notMem_closure_sdiff'`：indep_iff_forall_notMem_
closure_sdiff' : M.Indep I ↔ I subseteq M.E ∧ forall e in I, e ∉ M.closure (I \ 
{e})
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.mem_closure_of_mem`：mem_closure_of_mem (M : Matroid α) (h : e in
 X) (hX : X subseteq M.E
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_sdiff_distrib_left`：inter_sdiff_distrib_left (s t u : Set α) :
 s inter (t \ u) = (s inter t) \ (s inter u)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_singleton_eq_empty`：inter_singleton_eq_empty : s inter {a} = ∅
 ↔ a ∉ s
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma indep_iff_forall_closure_sdiff_ne :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → M.closure (I \ {e}) ≠ M.closure I := by
  rw [indep_iff_forall_notMem_closure_sdiff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h heI ?_,fun e heI hin ↦ h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_sdiff_distrib_left,
      inter_singleton_eq_empty.mpr heE, sdiff_empty, inter_comm, closure_inter_ground]
  nth_rw 2 [show I = insert e (I \ {e}) by simp [heI]]
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem hin, closure_closure]

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_closure_diff_ne := indep_iff_forall_closure_sdiff_ne
/-
**Matroid.Indep.union_indep_iff_forall_notMem_closure_right** 是 Mathlib 中的一个定理，位
于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I J : Set α},   M.Indep I → M.Indep J → 
(M.Indep (I ∪ J) ↔ ∀ e ∈ J \ I, e ∉ M.closure (I ∪ J \ {e}))
参数：M.Indep (I ∪ J) ↔ ∀ e ∈ J \ I, e ∉ M.closure (I ∪ J \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.notMem_closure_sdiff_of_mem`：∀ {α : Type u_2} {M : Matroid
 α} {e : α} {I : Set α}, M.Indep I → e ∈ I → e ∉ M.closure (I \ {e})
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `LE.le.eq_or_ssubset`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a = b ∨ a ⊂ b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
-/
lemma Indep.union_indep_iff_forall_notMem_closure_right (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I ∪ J) ↔ ∀ e ∈ J \ I, e ∉ M.closure (I ∪ (J \ {e})) := by
  refine ⟨fun h e heJ hecl ↦ h.notMem_closure_sdiff_of_mem (.inr heJ.1) ?_, fun h ↦ ?_⟩
  · rwa [union_sdiff_distrib, sdiff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_isBasis_of_subset (show I ⊆ I ∪ J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_ssubset
  · exact hKIJ.indep
  exfalso
  obtain ⟨e, heI, heK⟩ := exists_of_ssubset hssu
  have heJI : e ∈ J \ I := by
    rw [← union_sdiff_right, union_comm]
    exact ⟨heI, notMem_subset hK heK⟩
  refine h _ heJI ?_
  rw [← sdiff_singleton_eq_self heJI.2, ← union_sdiff_distrib]
  exact M.closure_subset_closure (subset_sdiff_singleton hKIJ.subset heK) <| hKIJ.subset_closure heI
/-
**Matroid.Indep.union_indep_iff_forall_notMem_closure_left** 是 Mathlib 中的一个定理，位于
命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I J : Set α},   M.Indep I → M.Indep J → 
(M.Indep (I ∪ J) ↔ ∀ e ∈ I \ J, e ∉ M.closure (I \ {e} ∪ J))
参数：M.Indep (I ∪ J) ↔ ∀ e ∈ I \ J, e ∉ M.closure (I \ {e} ∪ J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Matroid.Indep.union_indep_iff_forall_notMem_closure_right`：∀ {α : Type u
_2} {M : Matroid α} {I J : Set α},   M.Indep I → M.Indep J → (M.Indep (I ∪ J) ↔ 
∀ e ∈ J \ I, e ∉ M.closure (I ∪ J \ {e}))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Indep.union_indep_iff_forall_notMem_closure_left (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I ∪ J) ↔ ∀ e ∈ I \ J, e ∉ M.closure ((I \ {e}) ∪ J) := by
  simp_rw [union_comm I J, hJ.union_indep_iff_forall_notMem_closure_right hI, union_comm]
/-
**Matroid.Indep.closure_ssubset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep
`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I J : Set α}, M.Indep I → J ⊂ I → M.clos
ure J ⊂ M.closure I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `LE.le.ssubset_of_not_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α
] [inst : Preorder α] {a b : α}, a ⊆ b → ¬b ⊆ a → a ⊂ b
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Matroid.Indep.closure_inter_eq_self_of_subset`：∀ {α : Type u_2} {M : Mat
roid α} {I J : Set α}, M.Indep I → J ⊆ I → M.closure J ∩ I = J
· 使用引理 `Matroid.mem_closure_of_mem`：mem_closure_of_mem (M : Matroid α) (h : e in
 X) (hX : X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma Indep.closure_ssubset_closure (hI : M.Indep I) (hJI : J ⊂ I) : M.closure J ⊂ M.closure I := by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
  exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss ↦ heJ <|
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩
/-
**Matroid.indep_iff_forall_closure_ssubset_of_ssubset** 是 Mathlib 中的一个引理，位于命名空间 
`Matroid`。
形式化陈述：indep_iff_forall_closure_ssubset_of_ssubset (hI : I subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.closure_ssubset_closure`：∀ {α : Type u_2} {M : Matroid α} 
{I J : Set α}, M.Indep I → J ⊂ I → M.closure J ⊂ M.closure I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.indep_iff_forall_notMem_closure_sdiff`：indep_iff_forall_notMem_c
losure_sdiff (hI : I subseteq M.E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Set.sdiff_singleton_ssubset`：sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a i
n s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma indep_iff_forall_closure_ssubset_of_ssubset (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃J⦄, J ⊂ I → M.closure J ⊂ M.closure I := by
  refine ⟨fun h _ ↦ h.closure_ssubset_closure,
    fun h ↦ (indep_iff_forall_notMem_closure_sdiff hI).2 fun e heI hecl ↦ ?_⟩
  refine (h (sdiff_singleton_ssubset.2 heI)).ne ?_
  rw [show I = insert e (I \ {e}) by simp [heI], ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hecl]
  simp
/-
**Matroid.Indep.closure_sdiff_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.Indep I → (I ∩ X).Nonemp
ty → M.closure (I \ X) ⊂ M.closure I
参数：I ∩ X；I \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.closure_ssubset_closure`：∀ {α : Type u_2} {M : Matroid α} 
{I J : Set α}, M.Indep I → J ⊂ I → M.closure J ⊂ M.closure I
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
-/
lemma Indep.closure_sdiff_ssubset (hI : M.Indep I) (hX : (I ∩ X).Nonempty) :
    M.closure (I \ X) ⊂ M.closure I := by
  refine hI.closure_ssubset_closure <| sdiff_subset.ssubset_of_ne fun h ↦ ?_
  rw [sdiff_eq_left, disjoint_iff_inter_eq_empty] at h
  simp [h] at hX

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_ssubset := Indep.closure_sdiff_ssubset
/-
**Matroid.Indep.closure_sdiff_singleton_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → e ∈ I → 
M.closure (I \ {e}) ⊂ M.closure I
参数：I \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.closure_ssubset_closure`：∀ {α : Type u_2} {M : Matroid α} 
{I J : Set α}, M.Indep I → J ⊂ I → M.closure J ⊂ M.closure I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma Indep.closure_sdiff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
  hI.closure_ssubset_closure <| by simpa

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_singleton_ssubset := Indep.closure_sdiff_singleton_ssubset

end Indep

section insert

/-
**Matroid.mem_closure_insert** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_insert (he : e ∉ M.closure X) (hef : e in M.closure (insert f 
X)) : f in M.closure (insert e X)
参数：he : e ∉ M.closure X；hef : e in M.closure (insert f X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.insert_inter_of_notMem`：insert_inter_of_notMem (h : a ∉ t) : insert 
a s inter t = s inter t
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Set.insert_inter_of_mem`：insert_inter_of_mem (h : a in t) : insert a s i
nter t = insert a (s inter t)
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.Indep.notMem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {e : 
α} {I : Set α},   M.Indep I →     autoParam (e ∈ M.E) Matroid.Indep.notMem_closu
re_iff._auto_1 → (e ∉ …
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e ∈ M.closure (insert f X)) :
    f ∈ M.closure (insert e X) := by
  rw [← closure_inter_ground] at *
  have hfE : f ∈ M.E := by
    by_contra! hfE; rw [insert_inter_of_notMem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  rw [← hI.closure_eq_closure, hI.indep.notMem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    closure_insert_closure_eq_closure_insert, he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm,
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_closure_iff, or_iff_right (h.not_dep), mem_insert_iff,
    or_iff_left he.2] at hef
  subst hef; apply mem_insert
/-
**Matroid.closure_exchange** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_exchange (he : e in M.closure (insert f X) \ M.closure X) : f in M
.closure (insert e X) \ M.closure X
参数：he : e in M.closure (insert f X) \ M.closure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.mem_closure_insert`：mem_closure_insert (he : e ∉ M.closure X) (h
ef : e in M.closure (insert f X)) : f in M.closure (insert e X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false_intro`：∀ {a : Prop}, ¬a → (a ↔ False)
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `Set.sdiff_self`：sdiff_self {s : Set α} : s \ s = ∅
· 使用引理 `Matroid.closure_insert_eq_of_mem_closure`：closure_insert_eq_of_mem_closu
re (he : e in M.closure X) : M.closure (insert e X) = M.closure X
-/
lemma closure_exchange (he : e ∈ M.closure (insert f X) \ M.closure X) :
    f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf ↦ by
    rwa [closure_insert_eq_of_mem_closure hf, sdiff_self, iff_false_intro (notMem_empty _)] at he⟩
/-
**Matroid.closure_exchange_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_exchange_iff : e in M.closure (insert f X) \ M.closure X ↔ f in M.
closure (insert e X) \ M.closure X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_exchange`：closure_exchange (he : e in M.closure (insert 
f X) \ M.closure X) : f in M.closure (insert e X) \ M.closure X
-/
lemma closure_exchange_iff :
    e ∈ M.closure (insert f X) \ M.closure X ↔ f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩
/-
**Matroid.closure_insert_congr** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_insert_congr (he : e in M.closure (insert f X) \ M.closure X) : M.
closure (insert e X) = M.closure (insert f X)
参数：he : e in M.closure (insert f X) \ M.closure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_exchange`：closure_exchange (he : e in M.closure (insert 
f X) \ M.closure X) : f in M.closure (insert e X) \ M.closure X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
-/
lemma closure_insert_congr (he : e ∈ M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  have hf := closure_exchange he
  rw [eq_comm, ← closure_closure, ← insert_eq_of_mem he.1, closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_closure, ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hf.1, closure_closure, closure_closure]
/-
**Matroid.closure_sdiff_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_sdiff_eq_self (h : Y subseteq M.closure (X \ Y)) : M.closure (X \ 
Y) = M.closure X
参数：h : Y subseteq M.closure (X \ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `Matroid.closure_union_closure_left_eq`：∀ {α : Type u_2} (M : Matroid α) 
(X Y : Set α), M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y)
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma closure_sdiff_eq_self (h : Y ⊆ M.closure (X \ Y)) : M.closure (X \ Y) = M.closure X := by
  rw [← sdiff_union_inter X Y, ← closure_union_closure_left_eq,
    union_eq_self_of_subset_right (inter_subset_right.trans h), closure_closure, sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias closure_diff_eq_self := closure_sdiff_eq_self
/-
**Matroid.closure_sdiff_singleton_eq_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：closure_sdiff_singleton_eq_closure (h : e in M.closure (X \ {e})) : M.clos
ure (X \ {e}) = M.closure X
参数：h : e in M.closure (X \ {e})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_sdiff_eq_self`：closure_sdiff_eq_self (h : Y subseteq M.c
losure (X \ Y)) : M.closure (X \ Y) = M.closure X
-/
lemma closure_sdiff_singleton_eq_closure (h : e ∈ M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X :=
  closure_sdiff_eq_self (by simpa)

@[deprecated (since := "2026-06-03")]
alias closure_diff_singleton_eq_closure := closure_sdiff_singleton_eq_closure
/-
**Matroid.subset_closure_sdiff_iff_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid
`。
形式化陈述：subset_closure_sdiff_iff_closure_eq (h : Y subseteq X) (hY : Y subseteq M.
E
参数：h : Y subseteq X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_sdiff_eq_self`：closure_sdiff_eq_self (h : Y subseteq M.c
losure (X \ Y)) : M.closure (X \ Y) = M.closure X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.subset_closure_of_subset'`：subset_closure_of_subset' (M : Matroi
d α) (hXY : X subseteq Y) (hX : X subseteq M.E
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subset_closure_sdiff_iff_closure_eq (h : Y ⊆ X) (hY : Y ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure (X \ Y) ↔ M.closure (X \ Y) = M.closure X :=
  ⟨closure_sdiff_eq_self, fun h' ↦ (M.subset_closure_of_subset' h).trans h'.symm.subset⟩

@[deprecated (since := "2026-06-03")]
alias subset_closure_diff_iff_closure_eq := subset_closure_sdiff_iff_closure_eq
/-
**Matroid.mem_closure_sdiff_singleton_iff_closure** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：mem_closure_sdiff_singleton_iff_closure (he : e in X) (heE : e in M.E
参数：he : e in X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.subset_closure_sdiff_iff_closure_eq`：subset_closure_sdiff_iff_cl
osure_eq (h : Y subseteq X) (hY : Y subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma mem_closure_sdiff_singleton_iff_closure (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X := by
  simpa using subset_closure_sdiff_iff_closure_eq (Y := {e}) (X := X) (by simpa)

@[deprecated (since := "2026-06-03")]
alias mem_closure_diff_singleton_iff_closure := mem_closure_sdiff_singleton_iff_closure

end insert

/-
**Matroid.ext_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_closure {M₁ M₂ : Matroid α} (h : forall X, M₁.closure X = M₂.closure X
) : M₁ = M₂
参数：h : forall X, M₁.closure X = M₂.closure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.closure_univ`：∀ {α : Type u_2} (M : Matroid α), M.closure Set.un
iv = M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ext_closure {M₁ M₂ : Matroid α} (h : ∀ X, M₁.closure X = M₂.closure X) : M₁ = M₂ :=
  ext_indep (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_forall_closure_sdiff_ne, h])


section Spanning

variable {S T I B : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
a base of `M`. -/
@[mk_iff]
/-
**Matroid.Spanning** 是 Mathlib 中的一个结构，位于命名空间 `Matroid`。
形式化陈述：Spanning (M : Matroid α) (S : Set α) : Prop where closure_eq : M.closure S
 = M.E subset_ground : S subseteq M.E  attribute [aesop unsafe 10% (rule_sets
参数：M : Matroid α；S : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if 
it contains
a base of `M`.
-/
structure Spanning (M : Matroid α) (S : Set α) : Prop where
  closure_eq : M.closure S = M.E
  subset_ground : S ⊆ M.E

attribute [aesop unsafe 10% (rule_sets := [Matroid])] Spanning.subset_ground
/-
**Matroid.spanning_iff_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：spanning_iff_closure_eq (hS : S subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.spanning_iff`：∀ {α : Type u_2} (M : Matroid α) (S : Set α), M.Sp
anning S ↔ M.closure S = M.E ∧ S ⊆ M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spanning_iff_closure_eq (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.closure S = M.E := by
  rw [spanning_iff, and_iff_left hS]
/-
**Matroid.closure_spanning_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S : Set α},   autoParam (S ⊆ M.E) Matroi
d.closure_spanning_iff._auto_1 → (M.Spanning (M.closure S) ↔ M.Spanning S)
参数：S ⊆ M.E；M.Spanning (M.closure S) ↔ M.Spanning S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma closure_spanning_iff (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure_eq, closure_closure, ← spanning_iff_closure_eq]
/-
**Matroid.spanning_iff_ground_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：spanning_iff_ground_subset_closure (hS : S subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spanning_iff_ground_subset_closure (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.closure S := by
  rw [spanning_iff_closure_eq, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]
/-
**Matroid.not_spanning_iff_closure_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：not_spanning_iff_closure_ssubset (hS : S subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `iff_and_self`：∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `trivial`：True
-/
lemma not_spanning_iff_closure_ssubset (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure_eq, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial
/-
**Matroid.Spanning.superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S T : Set α},   M.Spanning S → S ⊆ T → a
utoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_1 → M.Spanning T
参数：T ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Spanning.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {S : Set α
}, M.Spanning S → M.closure S = M.E
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
-/
lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩
/-
**Matroid.Spanning.closure_eq_of_superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spa
nning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S T : Set α}, M.Spanning S → S ⊆ T → M.c
losure T = M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
-/
lemma Spanning.closure_eq_of_superset (hS : M.Spanning S) (hST : S ⊆ T) : M.closure T = M.E := by
  rw [← closure_inter_ground, ← spanning_iff_closure_eq]
  exact hS.superset (subset_inter hST hS.subset_ground)
/-
**Matroid.Spanning.union_left** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X S : Set α},   M.Spanning S → autoParam
 (X ⊆ M.E) Matroid.Spanning.union_left._auto_1 → M.Spanning (S ∪ X)
参数：X ⊆ M.E；S ∪ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
-/
lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) : M.Spanning (S ∪ X) :=
  hS.superset subset_union_left
/-
**Matroid.Spanning.union_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X S : Set α},   M.Spanning S → autoParam
 (X ⊆ M.E) Matroid.Spanning.union_right._auto_1 → M.Spanning (X ∪ S)
参数：X ⊆ M.E；X ∪ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
-/
lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right
/-
**Matroid.IsBase.spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M.IsBase B → M.Spanning B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
lemma IsBase.spanning (hB : M.IsBase B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩
/-
**Matroid.ground_spanning** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ground_spanning (M : Matroid α) : M.Spanning M.E
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.closure_ground`：∀ {α : Type u_2} (M : Matroid α), M.closure M.E 
= M.E
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩
/-
**Matroid.IsBase.spanning_of_superset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`
。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X B : Set α},   M.IsBase B → B ⊆ X → aut
oParam (X ⊆ M.E) Matroid.IsBase.spanning_of_superset._auto_1 → M.Spanning X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Matroid.IsBase.spanning`：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M
.IsBase B → M.Spanning B
-/
lemma IsBase.spanning_of_superset (hB : M.IsBase B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

/-- A version of `Matroid.spanning_iff_exists_isBase_subset` in which the `S ⊆ M.E` condition
appears in the RHS of the equivalence rather than as a hypothesis. -/
/-
**Matroid.spanning_iff_exists_isBase_subset'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：spanning_iff_exists_isBase_subset' : M.Spanning S ↔ (exists B, M.IsBase B 
∧ B subseteq S) ∧ S subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.Spanning.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {S : Set α
}, M.Spanning S → M.closure S = M.E
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Matroid.IsBase.spanning`：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M
.IsBase B → M.Spanning B

--- 原说明 ---
A version of `Matroid.spanning_iff_exists_isBase_subset` in which the `S ⊆ M.E` 
condition
appears in the RHS of the equivalence rather than as a hypothesis.
-/
lemma spanning_iff_exists_isBase_subset' : M.Spanning S ↔ (∃ B, M.IsBase B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine ⟨fun h ↦ ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis S
  have hB' := hB.isBasis_closure_right
  rw [h.closure_eq, isBasis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩
/-
**Matroid.spanning_iff_exists_isBase_subset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：spanning_iff_exists_isBase_subset (hS : S subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_exists_isBase_subset'`：spanning_iff_exists_isBase_s
ubset' : M.Spanning S ↔ (exists B, M.IsBase B ∧ B subseteq S) ∧ S subseteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spanning_iff_exists_isBase_subset (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.IsBase B ∧ B ⊆ S := by
  rw [spanning_iff_exists_isBase_subset', and_iff_left hS]
/-
**Matroid.Spanning.exists_isBase_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spann
ing`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S : Set α}, M.Spanning S → ∃ B, M.IsBase
 B ∧ B ⊆ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_exists_isBase_subset`：spanning_iff_exists_isBase_su
bset (hS : S subseteq M.E
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
-/
lemma Spanning.exists_isBase_subset (hS : M.Spanning S) : ∃ B, M.IsBase B ∧ B ⊆ S := by
  rwa [spanning_iff_exists_isBase_subset] at hS
/-
**Matroid.coindep_iff_compl_spanning** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：coindep_iff_compl_spanning (hI : I subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.coindep_iff_exists`：coindep_iff_exists (hX : X subseteq M.E
· 使用引理 `Matroid.spanning_iff_exists_isBase_subset`：spanning_iff_exists_isBase_su
bset (hS : S subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_exists_isBase_subset]
/-
**Matroid.spanning_iff_compl_coindep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：spanning_iff_compl_coindep (hS : S subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.coindep_iff_compl_spanning`：coindep_iff_compl_spanning (hI : I s
ubseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, sdiff_sdiff_cancel_left hS]
/-
**Matroid.Coindep.compl_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Coindep I → M.Spanning (M.
E \ I)
参数：M.E \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.coindep_iff_compl_spanning`：coindep_iff_compl_spanning (hI : I s
ubseteq M.E
· 使用定理 `Matroid.Coindep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.Coindep X → X ⊆ M.E
-/
lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI
/-
**Matroid.coindep_iff_closure_compl_eq_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid
`。
形式化陈述：coindep_iff_closure_compl_eq_ground (hK : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.coindep_iff_compl_spanning`：coindep_iff_compl_spanning (hI : I s
ubseteq M.E
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coindep_iff_closure_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_closure_eq]
/-
**Matroid.Coindep.closure_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α}, M.Coindep X → M.closure (M.E
 \ X) = M.E
参数：M.E \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.coindep_iff_closure_compl_eq_ground`：coindep_iff_closure_compl_e
q_ground (hK : X subseteq M.E
· 使用定理 `Matroid.Coindep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.Coindep X → X ⊆ M.E
-/
lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX
/-
**Matroid.Indep.isBase_of_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Indep I → M.Spanning I → M
.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
-/
lemma Indep.isBase_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.IsBase I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_isBase_subset; rwa [← hB.eq_of_subset_indep hI hBI]
/-
**Matroid.Spanning.isBase_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {I : Set α}, M.Spanning I → M.Indep I → M
.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {I : 
Set α}, M.Indep I → M.Spanning I → M.IsBase I
-/
lemma Spanning.isBase_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.IsBase I :=
  hI.isBase_of_spanning hIs
/-
**Matroid.Indep.eq_of_spanning_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S I : Set α}, M.Indep I → M.Spanning S →
 S ⊆ I → S = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `Matroid.Indep.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {I : 
Set α}, M.Indep I → M.Spanning I → M.IsBase I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
-/
lemma Indep.eq_of_spanning_subset (hI : M.Indep I) (hS : M.Spanning S) (hSI : S ⊆ I) : S = I :=
  ((hI.subset hSI).isBase_of_spanning hS).eq_of_subset_indep hI hSI
/-
**Matroid.IsBasis.spanning_iff_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I X → (M.Spannin
g I ↔ M.Spanning X)
参数：M.Spanning I ↔ M.Spanning X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `Matroid.IsBasis.left_subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I 
X : Set α}, M.IsBasis I X → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis.spanning_iff_spanning (hIX : M.IsBasis I X) : M.Spanning I ↔ M.Spanning X := by
  rw [spanning_iff_closure_eq, spanning_iff_closure_eq, hIX.closure_eq_closure]
/-
**Matroid.Spanning.isBase_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanni
ng`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S B : Set α}, M.Spanning S → ((M.restric
t S).IsBase B ↔ M.IsBase B ∧ B ⊆ S)
参数：(M.restrict S).IsBase B ↔ M.IsBase B ∧ B ⊆ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `Matroid.Indep.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {I : 
Set α}, M.Indep I → M.Spanning I → M.IsBase I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.spanning_iff_spanning`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → (M.Spanning I ↔ M.Spanning X)
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
-/
lemma Spanning.isBase_restrict_iff (hS : M.Spanning S) : (M ↾ S).IsBase B ↔ M.IsBase B ∧ B ⊆ S := by
  rw [isBase_restrict_iff', isBasis'_iff_isBasis]
  refine ⟨fun h ↦ ⟨?_, h.subset⟩, fun h ↦ h.1.indep.isBasis_of_subset_of_subset_closure h.2 ?_⟩
  · exact h.indep.isBase_of_spanning <| by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground
/-
**Matroid.Spanning.compl_coindep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S : Set α}, M.Spanning S → M.Coindep (M.
E \ S)
参数：M.E \ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.spanning_iff_compl_coindep`：spanning_iff_compl_coindep (hS : S s
ubseteq M.E
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
-/
lemma Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.E \ S) := by
  rwa [← spanning_iff_compl_coindep]
/-
**Matroid.IsBasis.isBase_of_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`
。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X I : Set α}, M.IsBasis I X → M.Spanning
 X → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {I : 
Set α}, M.Indep I → M.Spanning I → M.IsBase I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.spanning_iff_spanning`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → (M.Spanning I ↔ M.Spanning X)
-/
lemma IsBasis.isBase_of_spanning (hIX : M.IsBasis I X) (hX : M.Spanning X) : M.IsBase I :=
  hIX.indep.isBase_of_spanning <| by rwa [hIX.spanning_iff_spanning]
/-
**Matroid.Indep.exists_isBase_subset_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.Indep`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {S I : Set α}, M.Indep I → M.Spanning S →
 I ⊆ S → ∃ B, M.IsBase B ∧ I ⊆ B ∧ B ⊆ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `Matroid.IsBasis.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.Spanning X → M.IsBase I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
lemma Indep.exists_isBase_subset_spanning (hI : M.Indep I) (hS : M.Spanning S) (hIS : I ⊆ S) :
    ∃ B, M.IsBase B ∧ I ⊆ B ∧ B ⊆ S := by
  obtain ⟨B, hB⟩ := hI.subset_isBasis_of_subset hIS
  exact ⟨B, hB.1.isBase_of_spanning hS, hB.2, hB.1.subset⟩
/-
**Matroid.Restriction.isBase_iff_of_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Restriction`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {B : Set α} {N : Matroid α},   N.IsRestri
ction M → M.Spanning N.E → (N.IsBase B ↔ M.IsBase B ∧ B ⊆ N.E)
参数：N.IsBase B ↔ M.IsBase B ∧ B ⊆ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Spanning.isBase_restrict_iff`：∀ {α : Type u_2} {M : Matroid α} {
S B : Set α}, M.Spanning S → ((M.restrict S).IsBase B ↔ M.IsBase B ∧ B ⊆ S)
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Restriction.isBase_iff_of_spanning {N : Matroid α} (hR : N ≤r M) (hN : M.Spanning N.E) :
    N.IsBase B ↔ (M.IsBase B ∧ B ⊆ N.E) := by
  obtain ⟨R, hR : R ⊆ M.E, rfl⟩ := hR
  rw [Spanning.isBase_restrict_iff (show M.Spanning R from hN), restrict_ground_eq]
/-
**Matroid.ext_spanning** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_spanning {M M' : Matroid α} (h : M.E = M'.E) (hsp : forall S, S subset
eq M.E -> (M.Spanning S ↔ M'.Spanning S)) : M = M'
参数：h : M.E = M'.E；hsp : forall S, S subseteq M.E -> (M.Spanning S ↔ M'.Spanning 
S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用定理 `Matroid.ext_iff_indep`：ext_iff_indep {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ (M₁
.E = M₂.E) ∧ forall ⦃I⦄, I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I)
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.coindep_def`：coindep_def : M.Coindep X ↔ M✶.Indep X
· 使用引理 `Matroid.coindep_iff_compl_spanning`：coindep_iff_compl_spanning (hI : I s
ubseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma ext_spanning {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S)) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE])
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, ext_iff_indep, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]
/-
**Matroid.IsBase.eq_of_superset_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBa
se`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X B : Set α}, M.IsBase B → M.Spanning X 
→ X ⊆ B → B = X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.eq_of_subset_isBase`：∀ {α : Type u_1} {M : Matroid α} {B₁
 B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁ ⊆ B₂ → B₁ = B₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma IsBase.eq_of_superset_spanning (hB : M.IsBase B) (hX : M.Spanning X) (hXB : X ⊆ B) : B = X :=
  have ⟨B', hB', hB'X⟩ := hX.exists_isBase_subset
  subset_antisymm (by rwa [← hB'.eq_of_subset_isBase hB (hB'X.trans hXB)]) hXB
/-
**Matroid.isBase_iff_minimal_spanning** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBase_iff_minimal_spanning : M.IsBase B ↔ Minimal M.Spanning B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minimal_subset_iff`：minimal_subset_iff : Minimal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> t subseteq s -> s = t
· 使用定理 `Matroid.IsBase.spanning`：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M
.IsBase B → M.Spanning B
· 使用定理 `Matroid.IsBase.eq_of_superset_spanning`：∀ {α : Type u_2} {M : Matroid α}
 {X B : Set α}, M.IsBase B → M.Spanning X → X ⊆ B → B = X
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
-/
theorem isBase_iff_minimal_spanning : M.IsBase B ↔ Minimal M.Spanning B := by
  rw [minimal_subset_iff]
  refine ⟨fun h ↦ ⟨h.spanning, fun _ ↦ h.eq_of_superset_spanning⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_subset
  rwa [h' hB'.spanning hBB']
/-
**Matroid.Spanning.isBase_of_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning
`。
形式化陈述：∀ {α : Type u_2} {M : Matroid α} {X : Set α}, M.Spanning X → (∀ ⦃Y : Set α
⦄, M.Spanning Y → Y ⊆ X → X = Y) → M.IsBase X
参数：∀ ⦃Y : Set α⦄, M.Spanning Y → Y ⊆ X → X = Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_iff_minimal_spanning`：isBase_iff_minimal_spanning : M.IsB
ase B ↔ Minimal M.Spanning B
· 使用定理 `minimal_subset_iff`：minimal_subset_iff : Minimal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> t subseteq s -> s = t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
theorem Spanning.isBase_of_minimal (hX : M.Spanning X) (h : ∀ ⦃Y⦄, M.Spanning Y → Y ⊆ X → X = Y) :
    M.IsBase X := by
  rwa [isBase_iff_minimal_spanning, minimal_subset_iff, and_iff_right hX]

end Spanning

section Constructions

variable {R S : Set α}

/-
**Matroid.restrict_closure_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (M : Matroid α) (X R : Set α), (M.restrict R).closure X =
 M.closure (X ∩ R) ∩ R ∪ R \ M.E
参数：M : Matroid α；X R : Set α；M.restrict R；X ∩ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis'_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {R I X :
 Set α}, (M.restrict R).IsBasis' I X ↔ M.IsBasis' I (X ∩ R) ∧ I ⊆ R
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Matroid.Indep.mem_closure_iff'`：∀ {α : Type u_2} {M : Matroid α} {I : Se
t α} {x : α},   M.Indep I → (x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) →
 x ∈ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨hI', hIR⟩ := isBasis'_restrict_iff.1 hI
  ext e
  rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, hI.indep.mem_closure_iff', mem_union,
    mem_inter_iff, hI'.indep.mem_closure_iff', restrict_ground_eq, restrict_indep_iff, mem_sdiff]
  by_cases he : M.Indep (insert e I)
  · simp [he, and_comm, insert_subset_iff, hIR, (he.subset_ground (mem_insert ..)),
      imp_or_left_iff_true]
  tauto
/-
**Matroid.restrict_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_closure_eq (M : Matroid α) (hXR : X subseteq R) (hR : R subseteq 
M.E
参数：M : Matroid α；hXR : X subseteq R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', sdiff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]
/-
**Matroid.emptyOn_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (X : Set α), (Matroid.emptyOn α).closure X = ∅
参数：X : Set α；Matroid.emptyOn α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ :=
  (closure_subset_ground ..).antisymm <| empty_subset _
/-
**Matroid.loopyOn_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (E X : Set α), (Matroid.loopyOn E).closure X = E
参数：E X : Set α；Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.emptyOn_closure_eq`：∀ {α : Type u_2} (X : Set α), (Matroid.empty
On α).closure X = ∅
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E := by
  simp [loopyOn, restrict_closure_eq']
/-
**Matroid.loopyOn_spanning_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {X E : Set α}, (Matroid.loopyOn E).Spanning X ↔ X ⊆ E
参数：Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.spanning_iff`：∀ {α : Type u_2} (M : Matroid α) (S : Set α), M.Sp
anning S ↔ M.closure S = M.E ∧ S ⊆ M.E
· 使用定理 `Matroid.loopyOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.loo
pyOn E).closure X = E
· 使用定理 `Matroid.loopyOn_ground`：∀ {α : Type u_1} (E : Set α), (Matroid.loopyOn E
).E = E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma loopyOn_spanning_iff {E : Set α} : (loopyOn E).Spanning X ↔ X ⊆ E := by
  rw [spanning_iff, loopyOn_closure_eq, loopyOn_ground, and_iff_right rfl]
/-
**Matroid.freeOn_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (E X : Set α), (Matroid.freeOn E).closure X = X ∩ E
参数：E X : Set α；Matroid.freeOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.Indep.mem_closure_iff'`：∀ {α : Type u_2} {M : Matroid α} {I : Se
t α} {x : α},   M.Indep I → (x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) →
 x ∈ I))
· 使用定理 `Matroid.freeOn_indep`：freeOn_indep (hIE : I subseteq E) : (freeOn E).Ind
ep I
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma freeOn_closure_eq (E X : Set α) : (freeOn E).closure X = X ∩ E := by
  simp +contextual [← closure_inter_ground _ X, Set.ext_iff, and_comm,
    insert_subset_iff, freeOn_indep_iff, (freeOn_indep inter_subset_right).mem_closure_iff']
/-
**Matroid.uniqueBaseOn_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} (I E X : Set α), (Matroid.uniqueBaseOn I E).closure X = X
 ∩ I ∩ E ∪ E \ I
参数：I E X : Set α；Matroid.uniqueBaseOn I E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn.eq_1`：∀ {α : Type u_1} (I E : Set α), Matroid.uniqu
eBaseOn I E = (Matroid.freeOn I).restrict E
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Matroid.freeOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.free
On E).closure X = X ∩ E
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Matroid.freeOn_ground`：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E).
E = E
-/
@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X ∩ I ∩ E) ∪ (E \ I) := by
  rw [uniqueBaseOn, restrict_closure_eq', freeOn_closure_eq, inter_right_comm,
    inter_assoc (c := E), inter_self, inter_right_comm, freeOn_ground]
/-
**Matroid.closure_empty_eq_ground_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.ext_closure`：ext_closure {M₁ M₂ : Matroid α} (h : forall X, M₁.c
losure X = M₂.closure X) : M₁ = M₂
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loopyOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.loo
pyOn E).closure X = E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_mono`：closure_mono (M : Matroid α) : Monotone M.closure
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Matroid.loopyOn_ground`：∀ {α : Type u_1} (E : Set α), (Matroid.loopyOn E
).E = E
-/
lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure ?_, fun h ↦ by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq, ← h]
  exact M.closure_mono (empty_subset _)
/-
**Matroid.comap_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (M : Matroid β) (f : α → β) (X : Set α),  
 (M.comap f).closure X = f ⁻¹' M.closure (f '' X)
参数：M : Matroid β；f : α → β；X : Set α；M.comap f；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.comap_isBasis'_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{N : Matroid β} {I X : Set α},   (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) 
(f '' X) ∧ Set.I…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matroid.Indep.mem_closure_iff'`：∀ {α : Type u_2} {M : Matroid α} {I : Se
t α} {x : α},   M.Indep I → (x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) →
 x ∈ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.injOn_insert`：injOn_insert {f : α -> β} {s : Set α} {a : α} (has : a
 ∉ s) : Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  -- Use a choice of basis and extensionality to change the goal to a statement about independence.
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hIinj, -⟩ := comap_isBasis'_iff.1 hI
  simp_rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, Set.ext_iff,
    hI.indep.mem_closure_iff', comap_ground_eq, mem_preimage, hI'.indep.mem_closure_iff',
    comap_indep_iff, and_imp, mem_image, and_congr_right_iff, ← image_insert_eq]
  -- the lemma now easily follows by considering elements/non-elements of `I` separately.
  intro x hxE
  by_cases hxI : x ∈ I
  · simp [hxI, show ∃ y ∈ I, f y = f x from ⟨x, hxI, rfl⟩]
  simp [hxI, injOn_insert hxI, hIinj]
/-
**Matroid.map_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (M : Matroid α) (f : α → β) (hf : Set.InjO
n f M.E) (X : Set β),   (M.map f hf).closure X = f '' M.closure (f ⁻¹' X)
参数：M : Matroid α；f : α → β；hf : Set.InjOn f M.E；X : Set β；M.map f hf；f ⁻¹' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.Indep.mem_closure_iff'`：∀ {α : Type u_2} {M : Matroid α} {I : Se
t α} {x : α},   M.Indep I → (x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) →
 x ∈ I))
· 使用定理 `Matroid.Indep.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matr
oid α},   M.Indep I → ∀ (f : α → β) (hf : Set.InjOn f M.E), (M.map f hf).Indep (
f '' I)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用引理 `Matroid.map_image_indep_iff`：map_image_indep_iff {hf} {I : Set α} (hI : 
I subseteq M.E) : (M.map f hf).Indep (f '' I) ↔ M.Indep I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Matroid.map_ground`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f :
 α → β) (hf : Set.InjOn f M.E), (M.map f hf).E = f '' M.E
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
-/
@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  -- It is enough to prove that `map` and `closure` commute for `M`-independent sets.
  suffices aux : ∀ ⦃I⦄, M.Indep I → (M.map f hf).closure (f '' I) = f '' (M.closure I) by
    obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X ∩ M.E)
    rw [← closure_inter_ground, map_ground, ← M.closure_inter_ground, ← hI.closure_eq_closure,
      ← aux hI.indep, ← image_preimage_inter, ← (hI.map hf).closure_eq_closure]
  -- Let `I` be independent, and transform the goal using closure/independence lemmas
  refine fun I hI ↦ Set.ext fun e ↦ ?_
  simp only [(hI.map f hf).mem_closure_iff', map_ground, mem_image, map_indep_iff,
    forall_exists_index, and_imp, hI.mem_closure_iff']
  -- The goal now easily follows from the invariance of independence under maps.
  constructor
  · rintro ⟨⟨x, hxE, rfl⟩, h2⟩
    refine ⟨x, ⟨hxE, fun hI' ↦ ?_⟩, rfl⟩
    obtain ⟨y, hyI, hfy⟩ := h2 _ hI' image_insert_eq.symm
    rw [hf.eq_iff (hI.subset_ground hyI) hxE] at hfy
    rwa [← hfy]
  rintro ⟨x, ⟨hxE, hxi⟩, rfl⟩
  refine ⟨⟨x, hxE, rfl⟩, fun J hJ hJI ↦ ⟨x, hxi ?_, rfl⟩⟩
  replace hJ := hJ.map f hf
  have hrw := image_insert_eq ▸ hJI
  rwa [← hrw, map_image_indep_iff (insert_subset hxE hI.subset_ground)] at hJ
/-
**Matroid.restrict_spanning_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_spanning_iff (hSR : S subseteq R) (hR : R subseteq M.E
参数：hSR : S subseteq R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.spanning_iff`：∀ {α : Type u_2} (M : Matroid α) (S : Set α), M.Sp
anning S ↔ M.closure S = M.E ∧ S ⊆ M.E
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `Matroid.restrict_closure_eq`：restrict_closure_eq (M : Matroid α) (hXR : 
X subseteq R) (hR : R subseteq M.E
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_spanning_iff (hSR : S ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Spanning S ↔ R ⊆ M.closure S := by
  rw [spanning_iff, restrict_ground_eq, and_iff_left hSR, restrict_closure_eq _ hSR, inter_eq_right]
/-
**Matroid.restrict_spanning_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_spanning_iff' : (M ↾ R).Spanning S ↔ R inter M.E subseteq M.closu
re S ∧ S subseteq R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.spanning_iff`：∀ {α : Type u_2} (M : Matroid α) (S : Set α), M.Sp
anning S ↔ M.closure S = M.E ∧ S ⊆ M.E
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_spanning_iff' : (M ↾ R).Spanning S ↔ R ∩ M.E ⊆ M.closure S ∧ S ⊆ R := by
  rw [spanning_iff, restrict_closure_eq', restrict_ground_eq, and_congr_left_iff,
    sdiff_eq_compl_inter, ← union_inter_distrib_right, inter_eq_right, union_comm,
    ← sdiff_subset_iff, sdiff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

end Constructions

end Matroid

