/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Multiset.Pi
public import Mathlib.Logic.Function.DependsOn

/-!
# The Cartesian product of finsets

## Main definitions

* `Finset.pi`: Cartesian product of finsets indexed by a finset.
-/

@[expose] public section

open Function

namespace Finset

open Multiset

/-! ### pi -/


section Pi

variable {α : Type*}

/--
Definition of `Pi.empty` / `Pi.empty` 的定义

English:
definition Pi.empty
  signature: (β : α -> Sort*) (a : α) (h : a in (∅ : Finset α))
  body: Multiset.Pi.empty β a h

universe u v

中文:
定义 依赖函数类型.empty
  签名: (β : α -> 类型层*) (a : α) (h : a in (∅ : 有限集 α))
  定义体: Multiset.Pi.empty β a h

universe u v

Depends on / 依赖: Multiset, Multiset.Pi.empty, smul_assoc
-/
def Pi.empty (β : α -> Sort*) (a : α) (h : a in (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h

universe u v
variable {β : α -> Type u} {δ : α -> Sort v} {s : Finset α} {t : forall a, Finset (β a)}

section
variable [DecidableEq α]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (s : Finset α) (t : forall a, Finset (β a))
  body: ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]

中文:
定义 pi
  签名: (s : 有限集 α) (t : 对任意 a, 有限集 (β a))
  定义体: ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]

Depends on / 依赖: s.nodup.pi
-/
def pi (s : Finset α) (t : forall a, Finset (β a)) : Finset (forall a in s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]
/--
theorem `pi_val` / 定理 `pi_val`

English:
theorem pi_val
  given: (s : Finset α) (t : forall a, Finset (β a))
  statement: (s.pi t).1 = s.1.pi fun a => (t a).1
  proof: rfl

@[simp, grind =]

中文:
定理 pi_val
  条件: (s : 有限集 α) (t : 对任意 a, 有限集 (β a))
  结论: (s.pi t).1 = s.1.pi fun a => (t a).1
  证明: rfl

@[simp, grind =]
-/
theorem pi_val (s : Finset α) (t : forall a, Finset (β a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl

@[simp, grind =]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: {s : Finset α} {t : forall a, Finset (β a)} {f : forall a in s, β a}
  proof: Multiset.mem_pi _ _ _

中文:
定理 mem_pi
  条件: {s : 有限集 α} {t : 对任意 a, 有限集 (β a)} {f : 对任意 a in s, β a}
  证明: Multiset.mem_pi _ _ _

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, Multiset, Multiset.mem_pi, compHom, fast_instance, mem_pi, toMonoidHom, toRealHom, toRealHom.toMonoidHom
-/
theorem mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : forall a in s, β a} :
    f in s.pi t ↔ forall (a) (h : a in s), f a h in t a :=
  Multiset.mem_pi _ _ _

/--
Definition of `Pi.cons` / `Pi.cons` 的定义

English:
definition Pi.cons
  signature: (s : Finset α) (a : α) (b : δ a) (f : forall a, a in s -> δ a) (a' : α) (h : a' in insert a s)
  body: Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)

@[simp]

中文:
定义 依赖函数类型.cons
  签名: (s : 有限集 α) (a : α) (b : δ a) (f : 对任意 a, a in s -> δ a) (a' : α) (h : a' in insert a s)
  定义体: Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)

@[simp]

Depends on / 依赖: Module, Module.compHom, Multiset, Multiset.Pi.cons, Multiset.mem_cons, compHom, fast_instance, mem_cons, mem_insert, mem_insert.symm, toRealHom
-/
def Pi.cons (s : Finset α) (a : α) (b : δ a) (f : forall a, a in s -> δ a) (a' : α) (h : a' in insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)

@[simp]
/--
theorem `Pi.cons_same` / 定理 `Pi.cons_same`

English:
theorem Pi.cons_same
  given: (s : Finset α) (a : α) (b : δ a) (f : forall a, a in s -> δ a) (h : a in insert a s)
  proof: Multiset.Pi.cons_same _

中文:
定理 依赖函数类型.cons_same
  条件: (s : 有限集 α) (a : α) (b : δ a) (f : 对任意 a, a in s -> δ a) (h : a in insert a s)
  证明: Multiset.Pi.cons_same _

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, Multiset, Multiset.Pi.cons_same, algebraMap, commutes, cons_same, smul_def, toRealHom
-/
theorem Pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : forall a, a in s -> δ a) (h : a in insert a s) :
    Pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _

/--
theorem `Pi.cons_ne` / 定理 `Pi.cons_ne`

English:
theorem Pi.cons_ne
  statement: {s : Finset α} {a a' : α} {b : δ a} {f : forall a, a in s -> δ a} {h : a' in insert a s}
  proof: Multiset.Pi.cons_ne _ (Ne.symm ha)

中文:
定理 依赖函数类型.cons_ne
  结论: {s : 有限集 α} {a a' : α} {b : δ a} {f : 对任意 a, a in s -> δ a} {h : a' in insert a s}
  证明: Multiset.Pi.cons_ne _ (Ne.symm ha)

Depends on / 依赖: Multiset, Multiset.Pi.cons_ne, Ne.symm, cons_ne
-/
theorem Pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : forall a, a in s -> δ a} {h : a' in insert a s}
    (ha : a != a') : Pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ (Ne.symm ha)

/--
theorem `Pi.cons_injective` / 定理 `Pi.cons_injective`

English:
theorem Pi.cons_injective
  given: {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s)
  proof: fun e₁ e₂ eq =>
@Multiset.Pi.cons_injective α _ δ a b s.1 hs _ _
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) :=

中文:
定理 依赖函数类型.cons_injective
  条件: {a : α} {b : δ a} {s : 有限集 α} (hs : a ∉ s)
  证明: fun e₁ e₂ eq =>
@Multiset.Pi.cons_injective α _ δ a b s.1 hs _ _
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) :=
-/
theorem Pi.cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun e₁ e₂ eq =>
@Multiset.Pi.cons_injective α _ δ a b s.1 hs _ _
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) := by
          rw [eq]
        this

@[simp]
/--
theorem `pi_empty` / 定理 `pi_empty`

English:
theorem pi_empty
  given: {t : forall a : α, Finset (β a)}
  statement: pi (∅ : Finset α) t = singleton (Pi.empty β)
  proof: rfl

@[simp]

中文:
定理 pi_empty
  条件: {t : 对任意 a : α, 有限集 (β a)}
  结论: pi (∅ : 有限集 α) t = singleton (依赖函数类型.empty β)
  证明: rfl

@[simp]
-/
theorem pi_empty {t : forall a : α, Finset (β a)} : pi (∅ : Finset α) t = singleton (Pi.empty β) :=
  rfl

@[simp]
/--
lemma `pi_nonempty` / 引理 `pi_nonempty`

English:
lemma pi_nonempty
  statement: (s.pi t).Nonempty ↔ forall a in s, (t a).Nonempty
  proof: by
  simp [Finset.Nonempty, Classical.skolem]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, pi_nonempty_of_forall_nonempty⟩ := pi_nonempty

@[simp]

中文:
引理 pi_nonempty
  结论: (s.pi t).非空 ↔ 对任意 a in s, (t a).非空
  证明: by
  simp [Finset.Nonempty, Classical.skolem]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, pi_nonempty_of_forall_nonempty⟩ := pi_nonempty

@[simp]

Depends on / 依赖: Classical, Classical.skolem, Finset, Finset.Nonempty, Nonempty, skolem
-/
lemma pi_nonempty : (s.pi t).Nonempty ↔ forall a in s, (t a).Nonempty := by
  simp [Finset.Nonempty, Classical.skolem]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, pi_nonempty_of_forall_nonempty⟩ := pi_nonempty

@[simp]
/--
lemma `pi_eq_empty` / 引理 `pi_eq_empty`

English:
lemma pi_eq_empty
  statement: s.pi t = ∅ ↔ exists a in s, t a = ∅
  proof: by
  contrapose!; exact pi_nonempty

@[simp]

中文:
引理 pi_eq_empty
  结论: s.pi t = ∅ ↔ 存在 a in s, t a = ∅
  证明: by
  contrapose!; exact pi_nonempty

@[simp]

Depends on / 依赖: contrapose, pi_nonempty
-/
lemma pi_eq_empty : s.pi t = ∅ ↔ exists a in s, t a = ∅ := by
  contrapose!; exact pi_nonempty

@[simp]
/--
theorem `pi_insert` / 定理 `pi_insert`

English:
theorem pi_insert
  statement: [forall a, DecidableEq (β a)] {s : Finset α} {t : forall a : α, Finset (β a)} {a : α}
  proof: by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine
    (fun s' (h : s' = a ::ₘ s.1) =>
        (?_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
dedup
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a

中文:
定理 pi_insert
  结论: [对任意 a, DecidableEq (β a)] {s : 有限集 α} {t : 对任意 a : α, 有限集 (β a)} {a : α}
  证明: by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine
    (fun s' (h : s' = a ::ₘ s.1) =>
        (?_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
dedup
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a

Depends on / 依赖: Multiset, Multiset.Pi.cons, Multiset.Pi.cons_injective, Multiset.pi, cons_injective, dedup.symm, eq_of_veq, insert, insert_val_of_notMem, nodup.map, pi_cons
-/
theorem pi_insert [forall a, DecidableEq (β a)] {s : Finset α} {t : forall a : α, Finset (β a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).biUnion fun b => (pi s t).image (Pi.cons s a b) := by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine
    (fun s' (h : s' = a ::ₘ s.1) =>
        (?_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
dedup
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a' h' =>
                    Multiset.Pi.cons s.1 a b f a' (h ▸ h'))))
      _ (insert_val_of_notMem ha)
  subst s'; rw [pi_cons]
  congr; funext b
  exact ((pi s t).nodup.map <| Multiset.Pi.cons_injective ha).dedup.symm

/--
theorem `pi_singletons` / 定理 `pi_singletons`

English:
theorem pi_singletons
  given: {β : Type*} (s : Finset α) (f : α -> β)
  proof: by grind

中文:
定理 pi_singletons
  条件: {β : 类型} (s : 有限集 α) (f : α -> β)
  证明: by grind
-/
theorem pi_singletons {β : Type*} (s : Finset α) (f : α -> β) :
    (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a} := by grind

/--
theorem `pi_const_singleton` / 定理 `pi_const_singleton`

English:
theorem pi_const_singleton
  given: {β : Type*} (s : Finset α) (i : β)
  proof: pi_singletons s fun _ => i

中文:
定理 pi_const_singleton
  条件: {β : 类型} (s : 有限集 α) (i : β)
  证明: pi_singletons s fun _ => i

Depends on / 依赖: pi_singletons
-/
theorem pi_const_singleton {β : Type*} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i

/--
theorem `pi_subset` / 定理 `pi_subset`

English:
theorem pi_subset
  given: {s : Finset α} (t₁ t₂ : forall a, Finset (β a)) (h : forall a in s, t₁ a subseteq t₂ a)
  proof: fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)

中文:
定理 pi_subset
  条件: {s : 有限集 α} (t₁ t₂ : 对任意 a, 有限集 (β a)) (h : 对任意 a in s, t₁ a subseteq t₂ a)
  证明: fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)

Depends on / 依赖: mem_pi, mem_pi.mp
-/
theorem pi_subset {s : Finset α} (t₁ t₂ : forall a, Finset (β a)) (h : forall a in s, t₁ a subseteq t₂ a) :
    s.pi t₁ subseteq s.pi t₂ := fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)

/--
theorem `pi_disjoint_of_disjoint` / 定理 `pi_disjoint_of_disjoint`

English:
theorem pi_disjoint_of_disjoint
  statement: {δ : α -> Type*} {s : Finset α} (t₁ t₂ : forall a, Finset (δ a)) {a : α}
  proof: disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
      congr_fun (congr_fun eq₁₂ a) ha

中文:
定理 pi_disjoint_of_disjoint
  结论: {δ : α -> 类型} {s : 有限集 α} (t₁ t₂ : 对任意 a, 有限集 (δ a)) {a : α}
  证明: disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
      congr_fun (congr_fun eq₁₂ a) ha

Depends on / 依赖: congr_fun, disjoint_iff_ne, mem_pi, mem_pi.mp
-/
theorem pi_disjoint_of_disjoint {δ : α -> Type*} {s : Finset α} (t₁ t₂ : forall a, Finset (δ a)) {a : α}
    (ha : a in s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
      congr_fun (congr_fun eq₁₂ a) ha

end

/-! ### Diagonal -/

variable {ι : Type*} [DecidableEq (ι -> α)] {s : Finset α} {f : ι -> α}

/--
Definition of `piDiag` / `piDiag` 的定义

English:
definition piDiag
  signature: (s : Finset α) (ι : Type*) [DecidableEq (ι -> α)]
  body: s.image (const ι)

中文:
定义 piDiag
  签名: (s : 有限集 α) (ι : 类型) [DecidableEq (ι -> α)]
  定义体: s.image (const ι)

Depends on / 依赖: s.image
-/
def piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι -> α)] : Finset (ι -> α) := s.image (const ι)

/--
lemma `mem_piDiag` / 引理 `mem_piDiag`

English:
lemma mem_piDiag
  statement: f in s.piDiag ι ↔ exists a in s, const ι a = f
  proof: mem_image

中文:
引理 mem_piDiag
  结论: f in s.piDiag ι ↔ 存在 a in s, const ι a = f
  证明: mem_image
-/
@[simp] lemma mem_piDiag : f in s.piDiag ι ↔ exists a in s, const ι a = f := mem_image

/--
lemma `card_piDiag` / 引理 `card_piDiag`

English:
lemma card_piDiag
  given: (s : Finset α) (ι : Type*) [DecidableEq (ι -> α)] [Nonempty ι]
  proof: by rw [piDiag, card_image_of_injective _ const_injective]

中文:
引理 card_piDiag
  条件: (s : 有限集 α) (ι : 类型) [DecidableEq (ι -> α)] [非空 ι]
  证明: by rw [piDiag, card_image_of_injective _ const_injective]
-/
@[simp] lemma card_piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι -> α)] [Nonempty ι] :
    (s.piDiag ι).card = s.card := by rw [piDiag, card_image_of_injective _ const_injective]

/-! ### Restriction -/

variable {π : ι -> Type*}

/-- Restrict domain of a function `f` to a finite set `s`. -/
@[simp]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (s : Finset ι) (f : (i : ι) -> π i)
  body: fun x => f x

中文:
定义 restrict
  签名: (s : 有限集 ι) (f : (i : ι) -> π i)
  定义体: fun x => f x
-/
def restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i := fun x => f x

/--
theorem `restrict_def` / 定理 `restrict_def`

English:
theorem restrict_def
  given: (s : Finset ι)
  statement: s.restrict (π := π) = fun f x => f x
  proof: rfl

中文:
定理 restrict_def
  条件: (s : 有限集 ι)
  结论: s.restrict (π := π) = fun f x => f x
  证明: rfl
-/
theorem restrict_def (s : Finset ι) : s.restrict (π := π) = fun f x => f x := rfl

variable {s t u : Finset ι}

/--
theorem `_root_.Set.piCongrLeft_comp_domRestrict` / 定理 `_root_.Set.piCongrLeft_comp_domRestrict`

English:
theorem _root_.Set.piCongrLeft_comp_domRestrict
  proof: rfl

@[deprecated (since := "2026-07-19")]
alias _root_.Set.piCongrLeft_comp_restrict := _root_.Set.piCongrLeft_comp_domRestrict

中文:
定理 _root_.集合.piCongrLeft_comp_domRestrict
  证明: rfl

@[deprecated (since := "2026-07-19")]
alias _root_.Set.piCongrLeft_comp_restrict := _root_.Set.piCongrLeft_comp_domRestrict
-/
theorem _root_.Set.piCongrLeft_comp_domRestrict :
    (s.equivToSet.symm.piCongrLeft (fun i : s => π i)) ∘ (s : Set ι).domRestrict = s.restrict := rfl

@[deprecated (since := "2026-07-19")]
alias _root_.Set.piCongrLeft_comp_restrict := _root_.Set.piCongrLeft_comp_domRestrict

/--
theorem `piCongrLeft_comp_restrict` / 定理 `piCongrLeft_comp_restrict`

English:
theorem piCongrLeft_comp_restrict
  proof: rfl

中文:
定理 piCongrLeft_comp_restrict
  证明: rfl
-/
theorem piCongrLeft_comp_restrict :
    (s.equivToSet.piCongrLeft (fun i : s => π i)) ∘ s.restrict = (s : Set ι).domRestrict := rfl

/-- If a function `f` is restricted to a finite set `t`, and `s ⊆ t`,
this is the restriction to `s`. -/
@[simp]
/--
Definition of `restrict₂` / `restrict₂` 的定义

English:
definition restrict₂
  signature: (hst : s subseteq t) (f : (i : t) -> π i) (i : s)
  body: f ⟨i.1, hst i.2⟩

中文:
定义 restrict₂
  签名: (hst : s subseteq t) (f : (i : t) -> π i) (i : s)
  定义体: f ⟨i.1, hst i.2⟩
-/
def restrict₂ (hst : s subseteq t) (f : (i : t) -> π i) (i : s) : π i := f ⟨i.1, hst i.2⟩

/--
theorem `restrict₂_def` / 定理 `restrict₂_def`

English:
theorem restrict₂_def
  given: (hst : s subseteq t)
  statement: restrict₂ (π := π) hst = fun f x => f ⟨x.1, hst x.2⟩
  proof: rfl

中文:
定理 restrict₂_def
  条件: (hst : s subseteq t)
  结论: restrict₂ (π := π) hst = fun f x => f ⟨x.1, hst x.2⟩
  证明: rfl
-/
theorem restrict₂_def (hst : s subseteq t) : restrict₂ (π := π) hst = fun f x => f ⟨x.1, hst x.2⟩ := rfl

/--
theorem `restrict₂_comp_restrict` / 定理 `restrict₂_comp_restrict`

English:
theorem restrict₂_comp_restrict
  given: (hst : s subseteq t)
  proof: rfl

中文:
定理 restrict₂_comp_restrict
  条件: (hst : s subseteq t)
  证明: rfl

Depends on / 依赖: restrict, s.restrict, t.restrict
-/
theorem restrict₂_comp_restrict (hst : s subseteq t) :
    (restrict₂ (π := π) hst) ∘ t.restrict = s.restrict := rfl

/--
theorem `restrict₂_comp_restrict₂` / 定理 `restrict₂_comp_restrict₂`

English:
theorem restrict₂_comp_restrict₂
  given: (hst : s subseteq t) (htu : t subseteq u)
  proof: rfl

中文:
定理 restrict₂_comp_restrict₂
  条件: (hst : s subseteq t) (htu : t subseteq u)
  证明: rfl

Depends on / 依赖: hst.trans
-/
theorem restrict₂_comp_restrict₂ (hst : s subseteq t) (htu : t subseteq u) :
    (restrict₂ (π := π) hst) ∘ (restrict₂ htu) = restrict₂ (hst.trans htu) := rfl

/--
lemma `dependsOn_restrict` / 引理 `dependsOn_restrict`

English:
lemma dependsOn_restrict
  given: (s : Finset ι)
  statement: DependsOn (s.restrict (π := π)) s
  proof: (s : Set ι).dependsOn_domRestrict

中文:
引理 dependsOn_restrict
  条件: (s : 有限集 ι)
  结论: DependsOn (s.restrict (π := π)) s
  证明: (s : Set ι).dependsOn_domRestrict
-/
lemma dependsOn_restrict (s : Finset ι) : DependsOn (s.restrict (π := π)) s :=
  (s : Set ι).dependsOn_domRestrict

/--
lemma `restrict_preimage_univ` / 引理 `restrict_preimage_univ`

English:
lemma restrict_preimage_univ
  given: [DecidablePred (· in s)] (t : (i : s) -> Set (π i))
  proof: by
  ext
  simp_all

中文:
引理 restrict_preimage_univ
  条件: [DecidablePred (· in s)] (t : (i : s) -> 集合 (π i))
  证明: by
  ext
  simp_all
-/
lemma restrict_preimage_univ [DecidablePred (· in s)] (t : (i : s) -> Set (π i)) :
    s.restrict ⁻¹' (Set.univ.pi t) =
      Set.pi s (fun i => if h : i in s then t ⟨i, h⟩ else Set.univ) := by
  ext
  simp_all

/--
lemma `domRestrict_preimage` / 引理 `domRestrict_preimage`

English:
lemma domRestrict_preimage
  statement: [DecidableEq ι] {I : Set ι}
  proof: by
  grind

@[deprecated (since := "2026-07-19")] alias restrict_preimage := domRestrict_preimage

中文:
引理 domRestrict_preimage
  结论: [DecidableEq ι] {I : 集合 ι}
  证明: by
  grind

@[deprecated (since := "2026-07-19")] alias restrict_preimage := domRestrict_preimage
-/
lemma domRestrict_preimage [DecidableEq ι] {I : Set ι}
    [DecidablePred (· in I)] (s : Finset I) (u : (i : I) -> Set (π i)) :
    I.domRestrict ⁻¹' Set.pi s u =
      Set.pi (s.image Subtype.val) (fun i => if h : i in I then u ⟨i, h⟩ else .univ) := by
  grind

@[deprecated (since := "2026-07-19")] alias restrict_preimage := domRestrict_preimage

/--
lemma `restrict₂_preimage` / 引理 `restrict₂_preimage`

English:
lemma restrict₂_preimage
  given: [DecidablePred (· in s)] (hst : s subseteq t) (u : (i : s) -> Set (π i))
  proof: by
  grind [restrict₂]

中文:
引理 restrict₂_preimage
  条件: [DecidablePred (· in s)] (hst : s subseteq t) (u : (i : s) -> 集合 (π i))
  证明: by
  grind [restrict₂]
-/
lemma restrict₂_preimage [DecidablePred (· in s)] (hst : s subseteq t) (u : (i : s) -> Set (π i)) :
    (restrict₂ hst) ⁻¹' (Set.univ.pi u) =
      (@Set.univ t).pi (fun j => if h : j.1 in s then u ⟨j.1, h⟩ else Set.univ) := by
  grind [restrict₂]

end Pi

end Finset
