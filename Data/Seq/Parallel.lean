/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.WSeq.Relation

/-!
# Parallel computation

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/

@[expose] public section

universe u v

namespace Computation
open Stream'

variable {α : Type u} {β : Type v}

/-
**Computation.parallel.aux2** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def parallel.aux2 : List (Computation α) → α ⊕ (List (Computation α)) :=
  List.foldr
    (fun c o =>
      match o with
      | Sum.inl a => Sum.inl a
      | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
    (Sum.inr [])

set_option backward.privateInPublic true in
/-
**Computation.parallel.aux1** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def parallel.aux1 :
    List (Computation α) × WSeq (Computation α) →
      α ⊕ (List (Computation α) × WSeq (Computation α))
  | (l, S) =>
    rmap
      (fun l' =>
        match Seq.destruct S with
        | none => (l', Seq.nil)
        | some (none, S') => (l', S')
        | some (some c, S') => (c :: l', S'))
      (parallel.aux2 l)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
/-
**Computation.parallel** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：parallel (S : WSeq (Computation α)) : Computation α
参数：S : WSeq (Computation α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Parallel computation of an infinite stream of computations,
  taking the first result
-/
def parallel (S : WSeq (Computation α)) : Computation α :=
  corec parallel.aux1 ([], S)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Computation.terminates_parallel.aux** 是 Mathlib 中的一个定理，位于命名空间 `Computation.ter
minates_parallel`。
形式化陈述：∀ {α : Type u} {l : List (Computation α)} {S : Stream'.WSeq (Computation α
)} {c : Computation α},   c ∈ l → c.Terminates → (Computation.corec Computation.
parallel.aux1✝ (l, S)).Terminates
参数：Computation α；Computation α；Computation.corec Computation.parallel.aux1✝ (l, 
S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_pure`：destruct_eq_pure {s : Computation α} {a : 
α} : destruct s = Sum.inl a -> s = pure a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `Computation.think_terminates`：∀ {α : Type u} (s : Computation α) [s.Term
inates], s.think.Terminates
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem terminates_parallel.aux :
    ∀ {l : List (Computation α)} {S c},
      c ∈ l → Terminates c → Terminates (corec parallel.aux1 (l, S)) := by
  have lem1 :
    ∀ l S, (∃ a : α, parallel.aux2 l = Sum.inl a) → Terminates (corec parallel.aux1 (l, S)) := by
    intro l S e
    obtain ⟨a, e⟩ := e
    have : corec parallel.aux1 (l, S) = return a := by
      apply destruct_eq_pure
      simp only [parallel.aux1, rmap, corec_eq]
      rw [e]
    rw [this]
    exact ret_terminates a
  intro l S c m T
  revert l S
  apply @terminatesRecOn _ _ c T _ _
  · intro a l S m
    apply lem1
    induction l with | nil => simp at m | cons c l IH => ?_
    simp only [List.mem_cons] at m
    rcases m with e | m
    · rw [← e]
      simp only [parallel.aux2, rmap, List.foldr_cons, destruct_pure]
      split <;> simp
    · obtain ⟨a', e⟩ := IH m
      simp only [parallel.aux2, rmap, List.foldr_cons] at ⊢ e
      rw [e]
      exact ⟨a', rfl⟩
  · intro s IH l S m
    have H1 (l') (e' : parallel.aux2 l = Sum.inr l') : s ∈ l' := by
      induction l generalizing l' with | nil => simp at m | cons c l IH' => ?_
      simp only [List.mem_cons] at m
      rcases m with e | m <;> simp only [parallel.aux2, rmap, List.foldr_cons] at e'
      · rw [← e] at e'
        -- Porting note: `revert e'` is required.
        revert e'
        split
        · simp
        · simp only [destruct_think, Sum.inr.injEq]
          rintro rfl
          simp
      · rcases e : List.foldr (fun c o =>
            match o with
            | Sum.inl a => Sum.inl a
            | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
          (Sum.inr List.nil) l with a' | ls <;> simp only [rmap] at e <;> rw [e] at e'
        · contradiction
        have := IH' m _ e
        grind
    rcases h : parallel.aux2 l with a | l'
    · exact lem1 _ _ ⟨a, h⟩
    · have H2 : corec parallel.aux1 (l, S) = think _ := destruct_eq_think (by
        simp only [parallel.aux1, rmap, corec_eq]
        rw [h])
      rw [H2]
      refine @Computation.think_terminates _ _ ?_
      have := H1 _ h
      rcases Seq.destruct S with (_ | ⟨_ | c, S'⟩) <;> apply IH <;> simp [this]

set_option backward.isDefEq.respectTransparency false in
/-
**Computation.terminates_parallel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_parallel {S : WSeq (Computation α)} {c} (h : c in S) [T : Termi
nates c] : Terminates (parallel S)
参数：Computation α；h : c in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_parallel.aux`：∀ {α : Type u} {l : List (Computati
on α)} {S : Stream'.WSeq (Computation α)} {c : Computation α},   c ∈ l → c.Termi
nates → (Computation.core…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Computation.destruct_eq_pure`：destruct_eq_pure {s : Computation α} {a : 
α} : destruct s = Sum.inl a -> s = pure a
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `_private.Mathlib.Data.Seq.Parallel.0.Computation.parallel.aux1.eq_1`：∀ {
α : Type u} (l : List (Computation α)) (S : Stream'.WSeq (Computation α)),   Com
putation.parallel.aux1✝ (l, S) =     Computation.rmap    …
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `Computation.think_terminates`：∀ {α : Type u} (s : Computation α) [s.Term
inates], s.think.Terminates
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Stream'.Seq.get?_tail`：∀ {α : Type u} (s : Stream'.Seq α) (n : ℕ), s.tai
l.get? n = s.get? (n + 1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem terminates_parallel {S : WSeq (Computation α)} {c} (h : c ∈ S) [T : Terminates c] :
    Terminates (parallel S) := by
  suffices
    ∀ (n) (l : List (Computation α)) (S c),
      c ∈ l ∨ some (some c) = Seq.get? S n → Terminates c → Terminates (corec parallel.aux1 (l, S))
    from
    let ⟨n, h⟩ := h
    this n [] S c (Or.inr h) T
  intro n; induction n <;> intro l S c o T
  case zero =>
    rcases o with a | a
    · exact terminates_parallel.aux a T
    have H : Seq.destruct S = some (some c, Seq.tail S) := by simp [Seq.destruct, (· <$> ·), ← a]
    rcases h : parallel.aux2 l with a | l'
    · have C : corec parallel.aux1 (l, S) = pure a := by
        apply destruct_eq_pure
        rw [corec_eq, parallel.aux1]
        rw [h]
        simp only [rmap]
      rw [C]
      infer_instance
    · have C : corec parallel.aux1 (l, S) = _ := destruct_eq_think (by
        simp only [corec_eq, rmap, parallel.aux1.eq_1]
        rw [h, H])
      rw [C]
      refine @Computation.think_terminates _ _ ?_
      apply terminates_parallel.aux _ T
      simp
  case succ n IH =>
    rcases o with a | a
    · exact terminates_parallel.aux a T
    rcases h : parallel.aux2 l with a | l'
    · have C : corec parallel.aux1 (l, S) = pure a := by
        apply destruct_eq_pure
        rw [corec_eq, parallel.aux1]
        rw [h]
        simp only [rmap]
      rw [C]
      infer_instance
    · have C : corec parallel.aux1 (l, S) = _ := destruct_eq_think (by
        simp only [corec_eq, rmap, parallel.aux1.eq_1]
        rw [h])
      rw [C]
      refine @Computation.think_terminates _ _ ?_
      have TT : ∀ l', Terminates (corec parallel.aux1 (l', S.tail)) := by
        intro
        apply IH _ _ _ (Or.inr _) T
        rw [a, Seq.get?_tail]
      rcases e : Seq.get? S 0 with - | o
      · grind [Seq.get?_zero_eq_none, Seq.get?_nil]
      · have D : Seq.destruct S = some (o, S.tail) := by
          dsimp [Seq.destruct]
          rw [e]
          rfl
        rw [D]
        cases o <;> simp [TT]
/-
**Computation.exists_of_mem_parallel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_of_mem_parallel {S : WSeq (Computation α)} {a} (h : a in parallel S
) : exists c in S, a in c
参数：Computation α；h : a in parallel S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.destruct_eq_pure`：destruct_eq_pure {s : Computation α} {a : 
α} : destruct s = Sum.inl a -> s = pure a
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `Computation.think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s
 → a ∈ s.think
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Stream'.WSeq.notMem_nil`：notMem_nil (a : α) : a ∉ @nil α
· 使用定理 `Stream'.Seq.destruct_eq_cons`：destruct_eq_cons {s : Seq α} {a s'} : dest
ruct s = some (a, s') -> s = cons a s'
· 使用定理 `Stream'.Seq.mem_cons_of_mem`：∀ {α : Type u} (y : α) {a : α} {s : Stream'
.Seq α}, a ∈ s → a ∈ Stream'.Seq.cons y s
· 使用定理 `Stream'.Seq.mem_cons`：∀ {α : Type u} (a : α) (s : Stream'.Seq α), a ∈ St
ream'.Seq.cons a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem exists_of_mem_parallel {S : WSeq (Computation α)} {a} (h : a ∈ parallel S) :
    ∃ c ∈ S, a ∈ c := by
  suffices
    ∀ C, a ∈ C → ∀ (l : List (Computation α)) (S),
      corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c from
    let ⟨c, h1, h2⟩ := this _ h [] S rfl
    ⟨c, h1.resolve_left <| List.not_mem_nil, h2⟩
  let F : List (Computation α) → α ⊕ (List (Computation α)) → Prop := by
    intro l a
    rcases a with a | l'
    · exact ∃ c ∈ l, a ∈ c
    · exact ∀ a', (∃ c ∈ l', a' ∈ c) → ∃ c ∈ l, a' ∈ c
  have lem1 (l) : F l (parallel.aux2 l) := by
    induction l <;> simp only [parallel.aux2, List.foldr]
    case nil =>
      intro a h
      assumption
    case cons c l IH =>
      simp only [parallel.aux2] at IH
      -- Porting note: `revert IH` & `intro IH` are required.
      revert IH
      cases List.foldr (fun c o =>
        match o with
        | Sum.inl a => Sum.inl a
        | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c)) (Sum.inr List.nil) l <;>
        intro IH <;> simp only
      · rcases IH with ⟨c', cl, ac⟩
        exact ⟨c', List.Mem.tail _ cl, ac⟩
      · rcases h : destruct c with a | c' <;> simp only [rmap]
        · refine ⟨c, List.mem_cons_self, ?_⟩
          rw [destruct_eq_pure h]
          apply ret_mem
        · intro a' h
          rcases h with ⟨d, dm, ad⟩
          rcases List.mem_cons.mp dm with e | dl
          · rw [e] at ad
            refine ⟨c, List.mem_cons_self, ?_⟩
            rw [destruct_eq_think h]
            exact think_mem ad
          · obtain ⟨d, dm⟩ := IH a' ⟨d, dl, ad⟩
            obtain ⟨dm, ad⟩ := dm
            exact ⟨d, List.Mem.tail _ dm, ad⟩
  intro C aC
  -- Porting note: `revert this e'` & `intro this e'` are required.
  apply memRecOn aC <;> [skip; intro C' IH] <;> intro l S e <;> have e' := congr_arg destruct e <;>
    have := lem1 l <;> simp only [parallel.aux1, corec_eq, destruct_pure, destruct_think] at e' <;>
    revert this e' <;> rcases parallel.aux2 l with a' | l' <;> intro this e' <;>
    [injection e' with h'; injection e'; injection e'; injection e' with h']
  · rw [h'] at this
    rcases this with ⟨c, cl, ac⟩
    exact ⟨c, Or.inl cl, ac⟩
  · rcases e : Seq.destruct S with - | a <;> rw [e] at h'
    · exact
        let ⟨d, o, ad⟩ := IH _ _ h'
        let ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (WSeq.notMem_nil _), ad⟩
        ⟨c, Or.inl cl, ac⟩
    · obtain ⟨o, S'⟩ := a
      obtain - | c := o <;> simp only at h' <;> rcases IH _ _ h' with ⟨d, dl | dS', ad⟩
      · exact
          let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
          ⟨c, Or.inl cl, ac⟩
      · refine ⟨d, Or.inr ?_, ad⟩
        rw [Seq.destruct_eq_cons e]
        exact Seq.mem_cons_of_mem _ dS'
      · simp only [List.mem_cons] at dl
        rcases dl with dc | dl
        · rw [dc] at ad
          refine ⟨c, Or.inr ?_, ad⟩
          rw [Seq.destruct_eq_cons e]
          apply Seq.mem_cons
        · exact
            let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
            ⟨c, Or.inl cl, ac⟩
      · refine ⟨d, Or.inr ?_, ad⟩
        rw [Seq.destruct_eq_cons e]
        exact Seq.mem_cons_of_mem _ dS'
/-
**Computation.map_parallel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_parallel (f : α -> β) (S) : map f (parallel S) = parallel (S.map (map 
f))
参数：f : α -> β；S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Computation.destruct_map`：destruct_map (f : α -> β) (s) : destruct (map 
f s) = lmap f (rmap (map f) (destruct s))
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `_private.Mathlib.Data.Seq.Parallel.0.Computation.parallel.aux1.eq_1`：∀ {
α : Type u} (l : List (Computation α)) (S : Stream'.WSeq (Computation α)),   Com
putation.parallel.aux1✝ (l, S) =     Computation.rmap    …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Stream'.WSeq.seq_destruct_cons`：seq_destruct_cons (a : α) (s) : Seq.dest
ruct (cons a s) = some (some a, s)
· 使用定理 `Stream'.WSeq.map_cons`：map_cons (f : α -> β) (a s) : map f (cons a s) = 
cons (f a) (map f s)
· 使用定理 `Stream'.WSeq.seq_destruct_think`：seq_destruct_think (s : WSeq α) : Seq.d
estruct (think s) = some (none, s)
· 使用定理 `Stream'.WSeq.map_think`：map_think (f : α -> β) (s) : map f (think s) = t
hink (map f s)
-/
theorem map_parallel (f : α → β) (S) : map f (parallel S) = parallel (S.map (map f)) := by
  refine
    eq_of_bisim
      (fun c1 c2 =>
        ∃ l S,
          c1 = map f (corec parallel.aux1 (l, S)) ∧
            c2 = corec parallel.aux1 (l.map (map f), S.map (map f)))
      ?_ ⟨[], S, rfl, rfl⟩
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨l, S, rfl, rfl⟩ => by
      have : parallel.aux2 (l.map (map f))
          = lmap f (rmap (List.map (map f)) (parallel.aux2 l)) := by
        simp only [parallel.aux2, rmap, lmap]
        induction l with
        | nil => grind
        | cons => grind [destruct_map, lmap, rmap]
      simp only [BisimO, destruct_map, lmap, rmap, corec_eq, parallel.aux1.eq_1]
      rw [this]
      rcases parallel.aux2 l with a | l'
      · simp
      simp only [lmap, rmap]
      induction S using WSeq.recOn <;> simpa using ⟨_, _, rfl, rfl⟩
/-
**Computation.parallel_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：parallel_empty (S : WSeq (Computation α)) (h : S.head ~> none) : parallel 
S = empty _
参数：S : WSeq (Computation α)；h : S.head ~> none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_empty_of_not_terminates`：eq_empty_of_not_terminates {s} (
H : ¬Terminates s) : s = empty α
· 使用定理 `Computation.exists_of_mem_parallel`：exists_of_mem_parallel {S : WSeq (Co
mputation α)} {a} (h : a in parallel S) : exists c in S, a in c
· 使用定理 `Stream'.WSeq.exists_get?_of_mem`：∀ {α : Type u} {s : Stream'.WSeq α} {a 
: α}, a ∈ s → ∃ n, some a ∈ s.get? n
· 使用定理 `Stream'.WSeq.head_some_of_get?_some`：∀ {α : Type u} {s : Stream'.WSeq α}
 {a : α} {n : ℕ}, some a ∈ s.get? n → ∃ a', some a' ∈ s.head
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem parallel_empty (S : WSeq (Computation α)) (h : S.head ~> none) : parallel S = empty _ :=
  eq_empty_of_not_terminates fun ⟨⟨a, m⟩⟩ => by
    let ⟨c, cs, _⟩ := exists_of_mem_parallel m
    let ⟨n, nm⟩ := WSeq.exists_get?_of_mem cs
    let ⟨c', h'⟩ := WSeq.head_some_of_get?_some nm
    injection h h'

/-- Induction principle for parallel computations.
The reason this isn't trivial from `exists_of_mem_parallel` is because it eliminates to `Sort`. -/
/-
**Computation.parallelRec** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：parallelRec {S : WSeq (Computation α)} (C : α -> Sort v) (H : forall s in 
S, forall a in s, C a) {a} (h : a in parallel S) : C a
参数：Computation α；C : α -> Sort v；H : forall s in S, forall a in s, C a；h : a in 
parallel S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for parallel computations.
The reason this isn't trivial from `exists_of_mem_parallel` is because it elimin
ates to `Sort`.
-/
def parallelRec {S : WSeq (Computation α)} (C : α → Sort v) (H : ∀ s ∈ S, ∀ a ∈ s, C a) {a}
    (h : a ∈ parallel S) : C a := by
  let T : WSeq (Computation (α × Computation α)) := S.map fun c => c.map fun a => (a, c)
  have : S = T.map (map fun c => c.1) := by
    rw [← WSeq.map_comp]
    refine (WSeq.map_id _).symm.trans (congr_arg (fun f => WSeq.map f S) ?_)
    funext c
    dsimp [id, Function.comp_def]
    rw [← map_comp]
    exact (map_id _).symm
  have pe := congr_arg parallel this
  rw [← map_parallel] at pe
  have h' := h
  rw [pe] at h'
  haveI : Terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩
  rcases e : get (parallel T) with ⟨a', c⟩
  have : a ∈ c ∧ c ∈ S := by
    rcases exists_of_mem_map h' with ⟨d, dT, cd⟩
    rw [get_eq_of_mem _ dT] at e
    cases e
    dsimp at cd
    cases cd
    rcases exists_of_mem_parallel dT with ⟨d', dT', ad'⟩
    rcases WSeq.exists_of_mem_map dT' with ⟨c', cs', e'⟩
    rw [← e'] at ad'
    rcases exists_of_mem_map ad' with ⟨a', ac', e'⟩
    injection e' with i1 i2
    constructor
    · rwa [i1, i2] at ac'
    · rwa [i2] at cs'
  obtain ⟨ac, cs⟩ := this
  apply H _ cs _ ac
/-
**Computation.parallel_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：parallel_promises {S : WSeq (Computation α)} {a} (H : forall s in S, s ~> 
a) : parallel S ~> a
参数：Computation α；H : forall s in S, s ~> a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_parallel`：exists_of_mem_parallel {S : WSeq (Co
mputation α)} {a} (h : a in parallel S) : exists c in S, a in c
-/
theorem parallel_promises {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) : parallel S ~> a :=
  fun _ ma' =>
  let ⟨_, cs, ac⟩ := exists_of_mem_parallel ma'
  H _ cs ac
/-
**Computation.mem_parallel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_parallel {S : WSeq (Computation α)} {a} (H : forall s in S, s ~> a) {c
} (cs : c in S) (ac : a in c) : a in parallel S
参数：Computation α；H : forall s in S, s ~> a；cs : c in S；ac : a in c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.terminates_parallel`：terminates_parallel {S : WSeq (Computat
ion α)} {c} (h : c in S) [T : Terminates c] : Terminates (parallel S)
· 使用定理 `Computation.mem_of_promises`：mem_of_promises {a} (p : s ~> a) : a in s
· 使用定理 `Computation.parallel_promises`：parallel_promises {S : WSeq (Computation 
α)} {a} (H : forall s in S, s ~> a) : parallel S ~> a
-/
theorem mem_parallel {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) {c} (cs : c ∈ S)
    (ac : a ∈ c) : a ∈ parallel S := by
  have := terminates_of_mem ac
  have := terminates_parallel cs
  exact mem_of_promises _ (parallel_promises H)
/-
**Computation.parallel_congr_lem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：parallel_congr_lem {S T : WSeq (Computation α)} {a} (H : S.LiftRel Equiv T
) : (forall s in S, s ~> a) ↔ forall t in T, t ~> a
参数：Computation α；H : S.LiftRel Equiv T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.WSeq.exists_of_liftRel_right`：exists_of_liftRel_right {R : α -> 
β -> Prop} {s t} (H : LiftRel R s t) {b} (h : b in t) : exists a, a in s ∧ R a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.promises_congr`：promises_congr {c₁ c₂ : Computation α} (h : 
c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a
· 使用定理 `Stream'.WSeq.exists_of_liftRel_left`：exists_of_liftRel_left {R : α -> β 
-> Prop} {s t} (H : LiftRel R s t) {a} (h : a in s) : exists b, b in t ∧ R a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem parallel_congr_lem {S T : WSeq (Computation α)} {a} (H : S.LiftRel Equiv T) :
    (∀ s ∈ S, s ~> a) ↔ ∀ t ∈ T, t ~> a :=
  ⟨fun h1 _ tT =>
    let ⟨_, sS, se⟩ := WSeq.exists_of_liftRel_right H tT
    (promises_congr se _).1 (h1 _ sS),
    fun h2 _ sS =>
    let ⟨_, tT, se⟩ := WSeq.exists_of_liftRel_left H sS
    (promises_congr se _).2 (h2 _ tT)⟩

-- The parallel operation is only deterministic when all computation paths lead to the same value
/-
**Computation.parallel_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：parallel_congr_left {S T : WSeq (Computation α)} {a} (h1 : forall s in S, 
s ~> a) (H : S.LiftRel Equiv T) : parallel S ~ parallel T
参数：Computation α；h1 : forall s in S, s ~> a；H : S.LiftRel Equiv T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.parallel_congr_lem`：parallel_congr_lem {S T : WSeq (Computat
ion α)} {a} (H : S.LiftRel Equiv T) : (forall s in S, s ~> a) ↔ forall t in T, t
 ~> a
· 使用定理 `Computation.parallel_promises`：parallel_promises {S : WSeq (Computation 
α)} {a} (H : forall s in S, s ~> a) : parallel S ~> a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.exists_of_mem_parallel`：exists_of_mem_parallel {S : WSeq (Co
mputation α)} {a} (h : a in parallel S) : exists c in S, a in c
· 使用定理 `Stream'.WSeq.exists_of_liftRel_left`：exists_of_liftRel_left {R : α -> β 
-> Prop} {s t} (H : LiftRel R s t) {a} (h : a in s) : exists b, b in t ∧ R a b
· 使用定理 `Computation.mem_parallel`：mem_parallel {S : WSeq (Computation α)} {a} (H
 : forall s in S, s ~> a) {c} (cs : c in S) (ac : a in c) : a in parallel S
· 使用定理 `Stream'.WSeq.exists_of_liftRel_right`：exists_of_liftRel_right {R : α -> 
β -> Prop} {s t} (H : LiftRel R s t) {b} (h : b in t) : exists a, a in s ∧ R a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem parallel_congr_left {S T : WSeq (Computation α)} {a} (h1 : ∀ s ∈ S, s ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  let h2 := (parallel_congr_lem H).1 h1
  fun a' =>
  ⟨fun h => by
    have aa := parallel_promises h1 h
    rw [← aa]
    rw [← aa] at h
    exact
      let ⟨s, sS, as⟩ := exists_of_mem_parallel h
      let ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_left H sS
      let aT := (st _).1 as
      mem_parallel h2 tT aT,
    fun h => by
    have aa := parallel_promises h2 h
    rw [← aa]
    rw [← aa] at h
    exact
      let ⟨s, sS, as⟩ := exists_of_mem_parallel h
      let ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_right H sS
      let aT := (st _).2 as
      mem_parallel h1 tT aT⟩
/-
**Computation.parallel_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：parallel_congr_right {S T : WSeq (Computation α)} {a} (h2 : forall t in T,
 t ~> a) (H : S.LiftRel Equiv T) : parallel S ~ parallel T
参数：Computation α；h2 : forall t in T, t ~> a；H : S.LiftRel Equiv T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.parallel_congr_left`：parallel_congr_left {S T : WSeq (Comput
ation α)} {a} (h1 : forall s in S, s ~> a) (H : S.LiftRel Equiv T) : parallel S 
~ parallel T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computation.parallel_congr_lem`：parallel_congr_lem {S T : WSeq (Computat
ion α)} {a} (H : S.LiftRel Equiv T) : (forall s in S, s ~> a) ↔ forall t in T, t
 ~> a
-/
theorem parallel_congr_right {S T : WSeq (Computation α)} {a} (h2 : ∀ t ∈ T, t ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H

end Computation

