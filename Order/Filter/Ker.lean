/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Filter.Map

/-!
# Kernel of a filter

In this file we define the *kernel* `Filter.ker f` of a filter `f`
to be the intersection of all its sets.

We also prove that `Filter.principal` and `Filter.ker` form a Galois coinsertion
and prove other basic theorems about `Filter.ker`.
-/

@[expose] public section

open Function Set

namespace Filter

variable {ι : Sort*} {α β : Type*} {f g : Filter α} {s : Set α} {a : α}

/-
**Filter.ker_def** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：ker_def (f : Filter α) : f.ker = ⋂ s in f, s
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
-/
lemma ker_def (f : Filter α) : f.ker = ⋂ s ∈ f, s := sInter_eq_biInter
/-
**Filter.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {a : α}, a ∈ f.ker ↔ ∀ s ∈ f, a ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_sInter`：mem_sInter {x : α} {S : Set (Set α)} : x in ⋂₀ S ↔ foral
l t in S, x in t
-/
@[simp] lemma mem_ker : a ∈ f.ker ↔ ∀ s ∈ f, a ∈ s := mem_sInter
/-
**Filter.subset_ker** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {s : Set α}, s ⊆ f.ker ↔ ∀ t ∈ f, s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter_iff`：subset_sInter_iff {S : Set (Set α)} {t : Set α} :
 t subseteq ⋂₀ S ↔ forall t' in S, t subseteq t'
-/
@[simp] lemma subset_ker : s ⊆ f.ker ↔ ∀ t ∈ f, s ⊆ t := subset_sInter_iff

/-- `Filter.principal` forms a Galois coinsertion with `Filter.ker`. -/
/-
**Filter.giPrincipalKer** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：giPrincipalKer : GaloisCoinsertion (𝓟 : Set α -> Filter α) ker
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.principal` forms a Galois coinsertion with `Filter.ker`.
-/
def giPrincipalKer : GaloisCoinsertion (𝓟 : Set α → Filter α) ker :=
  GaloisConnection.toGaloisCoinsertion (fun s f ↦ by simp [principal_le_iff]) <| by
    simp only [subset_def, mem_ker, mem_principal]; aesop

@[deprecated (since := "2026-07-18")]
alias gi_principal_ker := giPrincipalKer
/-
**Filter.ker_mono** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：ker_mono : Monotone (ker : Filter α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
lemma ker_mono : Monotone (ker : Filter α → Set α) := giPrincipalKer.gc.monotone_u
/-
**Filter.ker_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：ker_surjective : Surjective (ker : Filter α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
lemma ker_surjective : Surjective (ker : Filter α → Set α) := giPrincipalKer.u_surjective
/-
**Filter.ker_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2}, ⊥.ker = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sInter_eq_empty_iff`：sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = 
∅ ↔ forall a, exists b in c, a ∉ b
· 使用定理 `trivial`：True
-/
@[simp] lemma ker_bot : ker (⊥ : Filter α) = ∅ := sInter_eq_empty_iff.2 fun _ ↦ ⟨∅, trivial, id⟩
/-
**Filter.ker_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2}, ⊤.ker = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
@[simp] lemma ker_top : ker (⊤ : Filter α) = univ := giPrincipalKer.gc.u_top
/-
**Filter.ker_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} {f : Filter α}, f.ker = Set.univ ↔ f = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `GaloisConnection.u_eq_top`：u_eq_top {l : α -> β} {u : β -> α} (gc : Galo
isConnection l u) {x} : u x = ⊤ ↔ l ⊤ <= x
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ker_eq_univ : ker f = univ ↔ f = ⊤ := giPrincipalKer.gc.u_eq_top.trans <| by simp
/-
**Filter.ker_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} (f g : Filter α), (f ⊓ g).ker = f.ker ∩ g.ker
参数：f g : Filter α；f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
@[simp] lemma ker_inf (f g : Filter α) : ker (f ⊓ g) = ker f ∩ ker g := giPrincipalKer.gc.u_inf
/-
**Filter.ker_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} (f : ι → Filter α), (⨅ i, f i).ker = ⋂ i, 
(f i).ker
参数：f : ι → Filter α；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
@[simp] lemma ker_iInf (f : ι → Filter α) : ker (⨅ i, f i) = ⋂ i, ker (f i) :=
  giPrincipalKer.gc.u_iInf
/-
**Filter.ker_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} (S : Set (Filter α)), (sInf S).ker = ⋂ f ∈ S, f.ker
参数：S : Set (Filter α)；sInf S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
@[simp] lemma ker_sInf (S : Set (Filter α)) : ker (sInf S) = ⋂ f ∈ S, ker f :=
  giPrincipalKer.gc.u_sInf
/-
**Filter.ker_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} (s : Set α), (Filter.principal s).ker = s
参数：s : Set α；Filter.principal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
@[simp] lemma ker_principal (s : Set α) : ker (𝓟 s) = s := giPrincipalKer.u_l_eq _
/-
**Filter.ker_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} (a : α), (pure a).ker = {a}
参数：a : α；pure a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.ker_principal`：∀ {α : Type u_2} (s : Set α), (Filter.principal s)
.ker = s
-/
@[simp] lemma ker_pure (a : α) : ker (pure a) = {a} := by rw [← principal_singleton, ker_principal]
/-
**Filter.ker_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (m : α → β) (f : Filter β), (Filter.comap 
m f).ker = m ⁻¹' f.ker
参数：m : α → β；f : Filter β；Filter.comap m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
@[simp] lemma ker_comap (m : α → β) (f : Filter β) : ker (comap m f) = m ⁻¹' ker f := by
  ext a
  simp only [mem_ker, mem_comap, forall_exists_index, and_imp, @forall_comm (Set α), mem_preimage]
  exact forall₂_congr fun s _ ↦ ⟨fun h ↦ h _ Subset.rfl, fun ha t ht ↦ ht ha⟩

@[simp]
/-
**Filter.ker_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ker_iSup (f : ι -> Filter α) : ker (⨆ i, f i) = ⋃ i, ker (f i)
参数：f : ι -> Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_iSup`：mem_iSup {x : Set α} {f : ι -> Filter α} : x in iSup f 
↔ forall i, x in f i
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用引理 `Filter.ker_mono`：ker_mono : Monotone (ker : Filter α -> Set α)
-/
theorem ker_iSup (f : ι → Filter α) : ker (⨆ i, f i) = ⋃ i, ker (f i) := by
  refine subset_antisymm (fun x hx ↦ ?_) ker_mono.le_map_iSup
  simp only [mem_iUnion, mem_ker] at hx ⊢
  contrapose! hx
  choose s hsf hxs using hx
  refine ⟨⋃ i, s i, ?_, by simpa⟩
  exact mem_iSup.2 fun i ↦ mem_of_superset (hsf i) (subset_iUnion s i)

@[simp]
/-
**Filter.ker_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ker_sSup (S : Set (Filter α)) : ker (sSup S) = ⋃ f in S, ker f
参数：S : Set (Filter α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Filter.ker_iSup`：ker_iSup (f : ι -> Filter α) : ker (⨆ i, f i) = ⋃ i, ke
r (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_sSup (S : Set (Filter α)) : ker (sSup S) = ⋃ f ∈ S, ker f := by
  simp [sSup_eq_iSup]

@[simp]
/-
**Filter.ker_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ker_sup (f g : Filter α) : ker (f ⊔ g) = ker f union ker g
参数：f g : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
· 使用定理 `Filter.ker_sSup`：ker_sSup (S : Set (Filter α)) : ker (sSup S) = ⋃ f in S
, ker f
· 使用定理 `Set.biUnion_pair`：biUnion_pair (a b : α) (s : α -> Set β) : ⋃ x in ({a, 
b} : Set α), s x = s a union s b
-/
theorem ker_sup (f g : Filter α) : ker (f ⊔ g) = ker f ∪ ker g := by
  rw [← sSup_pair, ker_sSup, biUnion_pair]

@[simp]
/-
**Filter.ker_prod** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：ker_prod (f : Filter α) (g : Filter β) : ker (f ×ˢ g) = ker f ×ˢ ker g
参数：f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ker_inf`：∀ {α : Type u_2} (f g : Filter α), (f ⊓ g).ker = f.ker ∩
 g.ker
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.ker_comap`：∀ {α : Type u_2} {β : Type u_3} (m : α → β) (f : Filte
r β), (Filter.comap m f).ker = m ⁻¹' f.ker
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_prod (f : Filter α) (g : Filter β) : ker (f ×ˢ g) = ker f ×ˢ ker g := by
  simp [Set.prod_eq, Filter.prod_eq_inf]

@[simp]
/-
**Filter.ker_pi** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：ker_pi {ι : Type*} {α : ι -> Type*} (f : (i : ι) -> Filter (α i)) : ker (F
ilter.pi f) = univ.pi (fun i => ker (f i))
参数：f : (i : ι) -> Filter (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ker_iInf`：∀ {ι : Sort u_1} {α : Type u_2} (f : ι → Filter α), (⨅ 
i, f i).ker = ⋂ i, (f i).ker
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.ker_comap`：∀ {α : Type u_2} {β : Type u_3} (m : α → β) (f : Filte
r β), (Filter.comap m f).ker = m ⁻¹' f.ker
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_pi {ι : Type*} {α : ι → Type*} (f : (i : ι) → Filter (α i)) :
    ker (Filter.pi f) = univ.pi (fun i => ker (f i)) := by
  simp [Set.pi_def, Filter.pi]

end Filter

