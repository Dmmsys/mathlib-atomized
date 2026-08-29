/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# The Cartesian product of multisets

## Main definitions

* `Multiset.pi`: Cartesian product of multisets indexed by a multiset.
-/

@[expose] public section


namespace Multiset

section Pi

open Function

namespace Pi
variable {α : Type*} [DecidableEq α] {δ : α -> Sort*}

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: (δ : α -> Sort*)
  body: nofun

中文:
定义 empty
  签名: (δ : α -> 类型层*)
  定义体: nofun
-/
def empty (δ : α -> Sort*) : forall a in (0 : Multiset α), δ a :=
  nofun

variable (m : Multiset α) (a : α)

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (b : δ a) (f : forall a in m, δ a)
  body: fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' (mem_cons.1 ha').resolve_left h

中文:
定义 cons
  签名: (b : δ a) (f : 对任意 a in m, δ a)
  定义体: fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' (mem_cons.1 ha').resolve_left h

Depends on / 依赖: Eq.ndrec, h.symm, mem_cons, resolve_left
-/
def cons (b : δ a) (f : forall a in m, δ a) : forall a' in a ::ₘ m, δ a' :=
fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' (mem_cons.1 ha').resolve_left h

variable {m a}

/--
theorem `cons_same` / 定理 `cons_same`

English:
theorem cons_same
  given: {b : δ a} {f : forall a in m, δ a} (h : a in a ::ₘ m)
  proof: dif_pos rfl

中文:
定理 cons_same
  条件: {b : δ a} {f : 对任意 a in m, δ a} (h : a in a ::ₘ m)
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem cons_same {b : δ a} {f : forall a in m, δ a} (h : a in a ::ₘ m) :
    cons m a b f a h = b :=
  dif_pos rfl

/--
theorem `cons_ne` / 定理 `cons_ne`

English:
theorem cons_ne
  statement: {a a' : α} {b : δ a} {f : forall a in m, δ a} (h' : a' in a ::ₘ m)
  proof: dif_neg h

中文:
定理 cons_ne
  结论: {a a' : α} {b : δ a} {f : 对任意 a in m, δ a} (h' : a' in a ::ₘ m)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ a} (h' : a' in a ::ₘ m)
    (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h

/--
theorem `cons_swap` / 定理 `cons_swap`

English:
theorem cons_swap
  statement: {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : forall a in m, δ a}
  proof: by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp]

中文:
定理 cons_swap
  结论: {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : 对任意 a in m, δ a}
  证明: by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Decidable.ne_or_eq, Multiset, Multiset.cons_swap, Pi.cons_ne, Pi.cons_same, all_goals, cons_ne, cons_same, cons_swap, eq_or_ne, heq_iff_eq, hfunext, ne_or_eq, on_goal
-/
theorem cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : forall a in m, δ a}
    (h : a != a') : Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f) ≍
      Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp]
/--
theorem `cons_eta` / 定理 `cons_eta`

English:
theorem cons_eta
  given: {m : Multiset α} {a : α} (f : forall a' in a ::ₘ m, δ a')
  proof: by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [Pi.cons_same]
  · rw [Pi.cons_ne _ h]

中文:
定理 cons_eta
  条件: {m : Multiset α} {a : α} (f : 对任意 a' in a ::ₘ m, δ a')
  证明: by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [Pi.cons_same]
  · rw [Pi.cons_ne _ h]

Depends on / 依赖: Pi.cons_ne, Pi.cons_same, cons_ne, cons_same
-/
theorem cons_eta {m : Multiset α} {a : α} (f : forall a' in a ::ₘ m, δ a') :
    (cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f := by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [Pi.cons_same]
  · rw [Pi.cons_ne _ h]

/--
theorem `cons_map` / 定理 `cons_map`

English:
theorem cons_map
  statement: (b : δ a) (f : forall a' in m, δ a')
  proof: by
  ext a' ha'
  refine (congrArg₂ _ ?_ rfl).trans (apply_dite (@φ _) (a' = a) _ _).symm
  ext rfl
  rfl

中文:
定理 cons_map
  结论: (b : δ a) (f : 对任意 a' in m, δ a')
  证明: by
  ext a' ha'
  refine (congrArg₂ _ ?_ rfl).trans (apply_dite (@φ _) (a' = a) _ _).symm
  ext rfl
  rfl

Depends on / 依赖: apply_dite
-/
theorem cons_map (b : δ a) (f : forall a' in m, δ a')
    {δ' : α -> Sort*} (φ : forall ⦃a'⦄, δ a' -> δ' a') :
    Pi.cons _ _ (φ b) (fun a' ha' => φ (f a' ha')) = (fun a' ha' => φ ((cons _ _ b f) a' ha')) := by
  ext a' ha'
  refine (congrArg₂ _ ?_ rfl).trans (apply_dite (@φ _) (a' = a) _ _).symm
  ext rfl
  rfl

/--
theorem `forall_rel_cons_ext` / 定理 `forall_rel_cons_ext`

English:
theorem forall_rel_cons_ext
  statement: {r : forall ⦃a⦄, δ a -> δ a -> Prop} {b₁ b₂ : δ a} {f₁ f₂ : forall a' in m, δ a'}
  proof: by
  intro a ha
  dsimp [cons]
  split_ifs with H
  · cases H
    exact hb
  · exact hf _ _

中文:
定理 对任意_rel_cons_ext
  结论: {r : 对任意 ⦃a⦄, δ a -> δ a -> 命题} {b₁ b₂ : δ a} {f₁ f₂ : 对任意 a' in m, δ a'}
  证明: by
  intro a ha
  dsimp [cons]
  split_ifs with H
  · cases H
    exact hb
  · exact hf _ _

Depends on / 依赖: split_ifs
-/
theorem forall_rel_cons_ext {r : forall ⦃a⦄, δ a -> δ a -> Prop} {b₁ b₂ : δ a} {f₁ f₂ : forall a' in m, δ a'}
    (hb : r b₁ b₂) (hf : forall (a : α) (ha : a in m), r (f₁ a ha) (f₂ a ha)) :
    forall a ha, r (cons _ _ b₁ f₁ a ha) (cons _ _ b₂ f₂ a ha) := by
  intro a ha
  dsimp [cons]
  split_ifs with H
  · cases H
    exact hb
  · exact hf _ _

/--
theorem `cons_injective` / 定理 `cons_injective`

English:
theorem cons_injective
  given: {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s)
  proof: fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
have ne : a != a' := fun h => hs h.symm ▸ h'
      have : a' in a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
               _ = Pi.cons s a b f₂ a' this := by rw [eq]
               _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]

中文:
定理 cons_injective
  条件: {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s)
  证明: fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
have ne : a != a' := fun h => hs h.symm ▸ h'
      have : a' in a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
               _ = Pi.cons s a b f₂ a' this := by rw [eq]
               _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]
-/
theorem cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
have ne : a != a' := fun h => hs h.symm ▸ h'
      have : a' in a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
               _ = Pi.cons s a b f₂ a' this := by rw [eq]
               _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]

end Pi

section
variable {α : Type*} [DecidableEq α] {β : α -> Type*}

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (m : Multiset α) (t : forall a, Multiset (β a))
  body: m.recOn {Pi.empty β}
    (fun a m (p : Multiset (forall a in m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp only [map_bind, map_map, comp_apply, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b _
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' _
        apply map_hcongr
        · rw [cons_swap a a']
        intro f _
        exact Pi.cons_swap eq)

@[simp]

中文:
定义 pi
  签名: (m : Multiset α) (t : 对任意 a, Multiset (β a))
  定义体: m.recOn {Pi.empty β}
    (fun a m (p : Multiset (forall a in m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp only [map_bind, map_map, comp_apply, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b _
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' _
        apply map_hcongr
        · rw [cons_swap a a']
        intro f _
        exact Pi.cons_swap eq)

@[simp]

Depends on / 依赖: Multiset, Pi.cons, Pi.cons_swap, Pi.empty, bind_bind, bind_hcongr, comp_apply, cons_swap, m.recOn, map_bind, map_hcongr, map_map, p.map
-/
def pi (m : Multiset α) (t : forall a, Multiset (β a)) : Multiset (forall a in m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (forall a in m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp only [map_bind, map_map, comp_apply, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b _
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' _
        apply map_hcongr
        · rw [cons_swap a a']
        intro f _
        exact Pi.cons_swap eq)

@[simp]
/--
theorem `pi_zero` / 定理 `pi_zero`

English:
theorem pi_zero
  given: (t : forall a, Multiset (β a))
  statement: pi 0 t = {Pi.empty β}
  proof: rfl

@[simp]

中文:
定理 pi_zero
  条件: (t : 对任意 a, Multiset (β a))
  结论: pi 0 t = {依赖函数类型.empty β}
  证明: rfl

@[simp]
-/
theorem pi_zero (t : forall a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl

@[simp]
/--
theorem `pi_cons` / 定理 `pi_cons`

English:
theorem pi_cons
  given: (m : Multiset α) (t : forall a, Multiset (β a)) (a : α)
  proof: recOn_cons a m

中文:
定理 pi_cons
  条件: (m : Multiset α) (t : 对任意 a, Multiset (β a)) (a : α)
  证明: recOn_cons a m

Depends on / 依赖: PUnit.unit, recOn_cons
-/
theorem pi_cons (m : Multiset α) (t : forall a, Multiset (β a)) (a : α) :
pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b :=
  recOn_cons a m

/--
theorem `card_pi` / 定理 `card_pi`

English:
theorem card_pi
  given: (m : Multiset α) (t : forall a, Multiset (β a))
  proof: Multiset.induction_on m (by simp) (by simp +contextual)

中文:
定理 card_pi
  条件: (m : Multiset α) (t : 对任意 a, Multiset (β a))
  证明: Multiset.induction_on m (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem card_pi (m : Multiset α) (t : forall a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp +contextual)

/--
theorem `Nodup.pi` / 定理 `Nodup.pi`

English:
theorem Nodup.pi
  given: {s : Multiset α} {t : forall a, Multiset (β a)}
  proof: Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp only [nodup_cons] at hs; exact hs.1
      have hs : Nodup s := by simp only [nodup_cons] at hs; exact hs.2
      simp only [pi_cons, nodup_bind]
      refine
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          ?_⟩
      refine (ht a <| mem_cons_self _ _).pairwise ?_
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons s a b₁ f a (mem_cons_self _ _) =
            Pi.cons s a b₂ g a (mem_cons_self _ _) := by rw [eq]
neb show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)

中文:
定理 Nodup.pi
  条件: {s : Multiset α} {t : 对任意 a, Multiset (β a)}
  证明: Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp only [nodup_cons] at hs; exact hs.1
      have hs : Nodup s := by simp only [nodup_cons] at hs; exact hs.2
      simp only [pi_cons, nodup_bind]
      refine
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          ?_⟩
      refine (ht a <| mem_cons_self _ _).pairwise ?_
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons s a b₁ f a (mem_cons_self _ _) =
            Pi.cons s a b₂ g a (mem_cons_self _ _) := by rw [eq]
neb show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)
-/
protected theorem Nodup.pi {s : Multiset α} {t : forall a, Multiset (β a)} :
    Nodup s -> (forall a in s, Nodup (t a)) -> Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp only [nodup_cons] at hs; exact hs.1
      have hs : Nodup s := by simp only [nodup_cons] at hs; exact hs.2
      simp only [pi_cons, nodup_bind]
      refine
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          ?_⟩
      refine (ht a <| mem_cons_self _ _).pairwise ?_
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons s a b₁ f a (mem_cons_self _ _) =
            Pi.cons s a b₂ g a (mem_cons_self _ _) := by rw [eq]
neb show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)

/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: (m : Multiset α) (t : forall a, Multiset (β a)) (f : forall a in m, β a)
  proof: by
  induction m using Multiset.induction_on with
  | empty =>
    have : f = Pi.empty β := funext (fun _ => funext fun h => (notMem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (notMem_zero _ h).elim
  | cons a m ih => ?_
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases h : a' = a
    · subst h
      rwa [Pi.cons_same]
    · rw [Pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), ?_⟩
    rw [Pi.cons_eta]

中文:
定理 mem_pi
  条件: (m : Multiset α) (t : 对任意 a, Multiset (β a)) (f : 对任意 a in m, β a)
  证明: by
  induction m using Multiset.induction_on with
  | empty =>
    have : f = Pi.empty β := funext (fun _ => funext fun h => (notMem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (notMem_zero _ h).elim
  | cons a m ih => ?_
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases h : a' = a
    · subst h
      rwa [Pi.cons_same]
    · rw [Pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), ?_⟩
    rw [Pi.cons_eta]

Depends on / 依赖: Multiset, Multiset.induction_on, Pi.cons_ne, Pi.cons_same, Pi.empty, cons_ne, cons_same, induction_on, mem_bind, mem_con, mem_cons_self, mem_map, mem_singleton, notMem_zero, pi_cons, pi_zero, simp_rw, true_iff
-/
theorem mem_pi (m : Multiset α) (t : forall a, Multiset (β a)) (f : forall a in m, β a) :
    f in pi m t ↔ forall (a) (h : a in m), f a h in t a := by
  induction m using Multiset.induction_on with
  | empty =>
    have : f = Pi.empty β := funext (fun _ => funext fun h => (notMem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (notMem_zero _ h).elim
  | cons a m ih => ?_
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases h : a' = a
    · subst h
      rwa [Pi.cons_same]
    · rw [Pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), ?_⟩
    rw [Pi.cons_eta]

end

end Pi

end Multiset
